// TreeCL Streams - ANSI CL I/O Abstraction
//
// Implements stream types for input/output operations.

use std::fs::File;
use std::io::{self, BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

/// Stream identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StreamId(pub u32);

/// Stream direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamDirection {
    Input,
    Output,
    Bidirectional,
}

/// Element type for streams
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamElementType {
    Character,
    Byte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenDirection {
    Input,
    Output,
    Io,
    Probe,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IfExists {
    Error,
    Supersede,
    NewVersion,
    Rename,
    RenameAndDelete,
    Append,
    Overwrite,
    Nil,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IfDoesNotExist {
    Error,
    Create,
    Nil,
}

/// Stream types
#[derive(Debug)]
pub enum Stream {
    /// Standard output (stdout)
    Stdout,
    /// Standard error (stderr)
    Stderr,
    /// Standard input (stdin)
    Stdin,
    /// String output stream - accumulates output to a string
    StringOutputStream {
        buffer: String,
    },
    /// String input stream - reads from a string
    StringInputStream {
        buffer: String,
        position: usize,
    },
    /// File stream
    FileOutputStream {
        path: String,
        file: File,
        element_type: StreamElementType,
    },
    FileInputStream {
        path: String,
        reader: BufReader<File>,
        element_type: StreamElementType,
    },
    FileIoStream {
        path: String,
        file: File,
        element_type: StreamElementType,
    },
    /// Broadcast stream - writes to multiple streams
    BroadcastStream {
        targets: Vec<StreamId>,
    },
    /// Two-way stream - combines input and output
    TwoWayStream {
        input: StreamId,
        output: StreamId,
    },
    /// Synonym stream - redirects to a dynamic variable
    SynonymStream {
        symbol_id: u32,
    },
    /// Echo stream - echoes input to output
    EchoStream {
        input: StreamId,
        output: StreamId,
    },
}

impl Stream {
    /// Get stream direction
    pub fn direction(&self) -> StreamDirection {
        match self {
            Stream::Stdout | Stream::Stderr | Stream::StringOutputStream { .. } 
            | Stream::FileOutputStream { .. } | Stream::BroadcastStream { .. } => {
                StreamDirection::Output
            }
            Stream::Stdin | Stream::StringInputStream { .. } | Stream::FileInputStream { .. } => {
                StreamDirection::Input
            }
            Stream::TwoWayStream { .. } | Stream::EchoStream { .. } => {
                StreamDirection::Bidirectional
            }
            Stream::FileIoStream { .. } => StreamDirection::Bidirectional,
            Stream::SynonymStream { .. } => StreamDirection::Bidirectional,
        }
    }
    
    /// Check if stream is open
    pub fn is_open(&self) -> bool {
        true // All streams in our Vec are open; closed streams are removed
    }
}

/// Stream manager - handles all stream operations
pub struct StreamManager {
    streams: Vec<Option<Stream>>,
    free_list: Vec<u32>,
    /// Current column position for fresh-line (per output stream)
    column_positions: crate::fastmap::HashMap<u32, usize>,
}

impl Default for StreamManager {
    fn default() -> Self {
        Self::new()
    }
}

impl StreamManager {
    /// Create a new stream manager with standard streams
    pub fn new() -> Self {
        let mut manager = Self {
            streams: Vec::new(),
            free_list: Vec::new(),
            column_positions: crate::fastmap::HashMap::default(),
        };
        
        // Allocate standard streams (IDs 0, 1, 2)
        let _stdin = manager.alloc(Stream::Stdin);   // 0
        let _stdout = manager.alloc(Stream::Stdout); // 1
        let _stderr = manager.alloc(Stream::Stderr); // 2
        
        manager
    }
    
    /// Standard stream IDs
    pub fn stdin_id(&self) -> StreamId { StreamId(0) }
    pub fn stdout_id(&self) -> StreamId { StreamId(1) }
    pub fn stderr_id(&self) -> StreamId { StreamId(2) }
    
    /// Allocate a new stream
    pub fn alloc(&mut self, stream: Stream) -> StreamId {
        if let Some(id) = self.free_list.pop() {
            self.streams[id as usize] = Some(stream);
            StreamId(id)
        } else {
            let id = self.streams.len() as u32;
            self.streams.push(Some(stream));
            StreamId(id)
        }
    }
    
    /// Get a stream by ID
    pub fn get(&self, id: StreamId) -> Option<&Stream> {
        self.streams.get(id.0 as usize).and_then(|s| s.as_ref())
    }
    
    /// Get a mutable stream by ID
    pub fn get_mut(&mut self, id: StreamId) -> Option<&mut Stream> {
        self.streams.get_mut(id.0 as usize).and_then(|s| s.as_mut())
    }
    
    /// Close a stream
    pub fn close(&mut self, id: StreamId) -> bool {
        self.close_with_abort(id, false)
    }

    pub fn close_with_abort(&mut self, id: StreamId, abort: bool) -> bool {
        if id.0 <= 2 {
            return false; // Can't close standard streams
        }
        if let Some(slot) = self.streams.get_mut(id.0 as usize) {
            if slot.is_some() {
                if !abort {
                    if let Some(stream) = slot.as_mut() {
                        match stream {
                            Stream::FileOutputStream { file, .. } => {
                                let _ = file.flush();
                            }
                            Stream::FileIoStream { file, .. } => {
                                let _ = file.flush();
                            }
                            _ => {}
                        }
                    }
                }
                *slot = None;
                self.free_list.push(id.0);
                self.column_positions.remove(&id.0);
                return true;
            }
        }
        false
    }

    fn path_plus_suffix(path: &Path, suffix: &str) -> PathBuf {
        let mut out = path.as_os_str().to_os_string();
        out.push(suffix);
        PathBuf::from(out)
    }

    fn first_available_suffix_path(path: &Path, base_suffix: &str) -> io::Result<PathBuf> {
        let first = Self::path_plus_suffix(path, base_suffix);
        if !first.exists() {
            return Ok(first);
        }
        for idx in 1..=1_000_000usize {
            let candidate = Self::path_plus_suffix(path, &format!("{}.{}", base_suffix, idx));
            if !candidate.exists() {
                return Ok(candidate);
            }
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "Could not find available backup filename for {}",
                path.display()
            ),
        ))
    }

    fn first_available_version_path(path: &Path) -> io::Result<PathBuf> {
        for version in 1..=1_000_000usize {
            let candidate = Self::path_plus_suffix(path, &format!(".~{}~", version));
            if !candidate.exists() {
                return Ok(candidate);
            }
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "Could not create :NEW-VERSION path for {}",
                path.display()
            ),
        ))
    }

    fn prepare_existing_file(path: &Path, if_exists: IfExists) -> io::Result<Option<PathBuf>> {
        match if_exists {
            IfExists::Rename => {
                let backup = Self::first_available_suffix_path(path, ".bak")?;
                std::fs::rename(path, &backup)?;
                Ok(None)
            }
            IfExists::RenameAndDelete => {
                let backup = Self::first_available_suffix_path(path, ".tmp-old")?;
                std::fs::rename(path, &backup)?;
                Ok(Some(backup))
            }
            IfExists::NewVersion => {
                let versioned = Self::first_available_version_path(path)?;
                std::fs::rename(path, &versioned)?;
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    pub fn open_file(
        &mut self,
        path: &str,
        direction: OpenDirection,
        if_exists: IfExists,
        if_does_not_exist: IfDoesNotExist,
        element_type: StreamElementType,
    ) -> io::Result<Option<StreamId>> {
        use std::io::ErrorKind;
        let path_ref = Path::new(path);
        let exists = path_ref.exists();

        match direction {
            OpenDirection::Input | OpenDirection::Probe => {
                if !exists {
                    match if_does_not_exist {
                        IfDoesNotExist::Nil => return Ok(None),
                        IfDoesNotExist::Error => {
                            return Err(io::Error::new(
                                ErrorKind::NotFound,
                                format!("No such file: {}", path),
                            ))
                        }
                        IfDoesNotExist::Create => {
                            let _ = std::fs::OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(false)
                                .open(path)?;
                        }
                    }
                }
                let file = std::fs::OpenOptions::new().read(true).open(path)?;
                let id = self.alloc(Stream::FileInputStream {
                    path: path.to_string(),
                    reader: BufReader::new(file),
                    element_type,
                });
                Ok(Some(id))
            }
            OpenDirection::Output => {
                if exists {
                    match if_exists {
                        IfExists::Nil => return Ok(None),
                        IfExists::Error => {
                            return Err(io::Error::new(
                                ErrorKind::AlreadyExists,
                                format!("File exists: {}", path),
                            ))
                        }
                        _ => {}
                    }
                } else {
                    match if_does_not_exist {
                        IfDoesNotExist::Nil => return Ok(None),
                        IfDoesNotExist::Error => {
                            return Err(io::Error::new(
                                ErrorKind::NotFound,
                                format!("No such file: {}", path),
                            ))
                        }
                        IfDoesNotExist::Create => {}
                    }
                }

                let cleanup_backup = if exists {
                    Self::prepare_existing_file(path_ref, if_exists)?
                } else {
                    None
                };

                let mut opts = std::fs::OpenOptions::new();
                match if_exists {
                    IfExists::Append => {
                        opts.append(true).create(true);
                    }
                    IfExists::Overwrite => {
                        opts.write(true).create(matches!(if_does_not_exist, IfDoesNotExist::Create));
                    }
                    IfExists::Error | IfExists::Nil => {
                        opts.write(true).create(matches!(if_does_not_exist, IfDoesNotExist::Create));
                    }
                    _ => {
                        opts.write(true).create(true).truncate(true);
                    }
                }
                if !exists && matches!(if_does_not_exist, IfDoesNotExist::Create) {
                    opts.create(true);
                }
                let file = opts.open(path)?;
                if let Some(old_path) = cleanup_backup {
                    let _ = std::fs::remove_file(old_path);
                }
                let id = self.alloc(Stream::FileOutputStream {
                    path: path.to_string(),
                    file,
                    element_type,
                });
                Ok(Some(id))
            }
            OpenDirection::Io => {
                if exists {
                    match if_exists {
                        IfExists::Nil => return Ok(None),
                        IfExists::Error => {
                            return Err(io::Error::new(
                                ErrorKind::AlreadyExists,
                                format!("File exists: {}", path),
                            ))
                        }
                        _ => {}
                    }
                } else {
                    match if_does_not_exist {
                        IfDoesNotExist::Nil => return Ok(None),
                        IfDoesNotExist::Error => {
                            return Err(io::Error::new(
                                ErrorKind::NotFound,
                                format!("No such file: {}", path),
                            ))
                        }
                        IfDoesNotExist::Create => {}
                    }
                }

                let cleanup_backup = if exists {
                    Self::prepare_existing_file(path_ref, if_exists)?
                } else {
                    None
                };

                let mut opts = std::fs::OpenOptions::new();
                opts.read(true).write(true);
                if !exists && matches!(if_does_not_exist, IfDoesNotExist::Create) {
                    opts.create(true);
                }
                match if_exists {
                    IfExists::Append => {
                        opts.append(true);
                    }
                    IfExists::Supersede
                    | IfExists::NewVersion
                    | IfExists::Rename
                    | IfExists::RenameAndDelete => {
                        opts.truncate(true).create(true);
                    }
                    _ => {}
                }
                let file = opts.open(path)?;
                if let Some(old_path) = cleanup_backup {
                    let _ = std::fs::remove_file(old_path);
                }
                let id = self.alloc(Stream::FileIoStream {
                    path: path.to_string(),
                    file,
                    element_type,
                });
                Ok(Some(id))
            }
        }
    }
    
    /// Write a string to a stream
    pub fn write_string(&mut self, id: StreamId, s: &str) -> io::Result<()> {
        // Track column position
        let col = self.column_positions.entry(id.0).or_insert(0);
        for c in s.chars() {
            if c == '\n' {
                *col = 0;
            } else {
                *col += 1;
            }
        }
        
        match self.get_mut(id) {
            Some(Stream::Stdout) => {
                print!("{}", s);
                io::stdout().flush()?;
                Ok(())
            }
            Some(Stream::Stderr) => {
                eprint!("{}", s);
                io::stderr().flush()?;
                Ok(())
            }
            Some(Stream::StringOutputStream { buffer }) => {
                buffer.push_str(s);
                Ok(())
            }
            Some(Stream::FileOutputStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character output stream",
                    ));
                }
                file.write_all(s.as_bytes())?;
                Ok(())
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character output stream",
                    ));
                }
                file.write_all(s.as_bytes())?;
                Ok(())
            }
            Some(Stream::BroadcastStream { targets }) => {
                let targets_copy: Vec<StreamId> = targets.clone();
                for target_id in targets_copy {
                    self.write_string(target_id, s)?;
                }
                Ok(())
            }
            Some(Stream::TwoWayStream { output, .. }) => {
                let out_id = *output;
                self.write_string(out_id, s)
            }
            Some(Stream::EchoStream { output, .. }) => {
                let out_id = *output;
                self.write_string(out_id, s)
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not an output stream")),
        }
    }
    
    /// Write a character to a stream
    pub fn write_char(&mut self, id: StreamId, c: char) -> io::Result<()> {
        self.write_string(id, &c.to_string())
    }
    
    /// Write a newline
    pub fn write_newline(&mut self, id: StreamId) -> io::Result<()> {
        self.write_string(id, "\n")
    }
    
    /// Fresh line - write newline only if not at column 0
    pub fn fresh_line(&mut self, id: StreamId) -> io::Result<bool> {
        let col = *self.column_positions.get(&id.0).unwrap_or(&0);
        if col != 0 {
            self.write_newline(id)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    /// Read a character from a stream
    pub fn read_char(&mut self, id: StreamId) -> io::Result<Option<char>> {
        match self.get_mut(id) {
            Some(Stream::Stdin) => {
                let mut buf = [0u8; 4];
                let stdin = io::stdin();
                let mut handle = stdin.lock();
                match handle.read(&mut buf[..1]) {
                    Ok(0) => Ok(None),
                    Ok(_) => {
                        // Simple ASCII for now
                        Ok(Some(buf[0] as char))
                    }
                    Err(e) => Err(e),
                }
            }
            Some(Stream::StringInputStream { buffer, position }) => {
                let chars: Vec<char> = buffer.chars().collect();
                if *position < chars.len() {
                    let c = chars[*position];
                    *position += 1;
                    Ok(Some(c))
                } else {
                    Ok(None)
                }
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut buf = [0u8; 1];
                match reader.read(&mut buf) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(buf[0] as char)),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut buf = [0u8; 1];
                match file.read(&mut buf) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(buf[0] as char)),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::TwoWayStream { input, .. }) => {
                let in_id = *input;
                self.read_char(in_id)
            }
            Some(Stream::EchoStream { input, output, .. }) => {
                let in_id = *input;
                let out_id = *output;
                let result = self.read_char(in_id)?;
                if let Some(c) = result {
                    self.write_char(out_id, c)?;
                }
                Ok(result)
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not an input stream")),
        }
    }
    
    /// Read a line from a stream
    pub fn read_line(&mut self, id: StreamId) -> io::Result<Option<String>> {
        match self.get_mut(id) {
            Some(Stream::Stdin) => {
                let mut line = String::new();
                let stdin = io::stdin();
                match stdin.lock().read_line(&mut line) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(line)),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::StringInputStream { buffer, position }) => {
                let remaining = &buffer[*position..];
                if remaining.is_empty() {
                    return Ok(None);
                }
                if let Some(nl_pos) = remaining.find('\n') {
                    let line = remaining[..=nl_pos].to_string();
                    *position += nl_pos + 1;
                    Ok(Some(line))
                } else {
                    let line = remaining.to_string();
                    *position = buffer.len();
                    Ok(Some(line))
                }
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(line)),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut out = String::new();
                let mut b = [0u8; 1];
                loop {
                    match file.read(&mut b) {
                        Ok(0) => {
                            if out.is_empty() {
                                return Ok(None);
                            }
                            return Ok(Some(out));
                        }
                        Ok(_) => {
                            out.push(b[0] as char);
                            if b[0] == b'\n' {
                                return Ok(Some(out));
                            }
                        }
                        Err(e) => return Err(e),
                    }
                }
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not an input stream")),
        }
    }
    
    /// Peek at next character without consuming
    pub fn peek_char(&mut self, id: StreamId) -> io::Result<Option<char>> {
        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, position }) => {
                let chars: Vec<char> = buffer.chars().collect();
                if *position < chars.len() {
                    Ok(Some(chars[*position]))
                } else {
                    Ok(None)
                }
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let buf = reader.fill_buf()?;
                if buf.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(buf[0] as char))
                }
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let pos = file.stream_position()?;
                let mut b = [0u8; 1];
                let result = match file.read(&mut b) {
                    Ok(0) => None,
                    Ok(_) => Some(b[0] as char),
                    Err(e) => return Err(e),
                };
                file.seek(SeekFrom::Start(pos))?;
                Ok(result)
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Cannot peek on this stream")),
        }
    }
    
    /// Unread a character (push back)
    pub fn unread_char(&mut self, id: StreamId, _c: char) -> io::Result<()> {
        match self.get_mut(id) {
            Some(Stream::StringInputStream { position, .. }) => {
                if *position > 0 {
                    *position -= 1;
                }
                Ok(())
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let pos = file.stream_position()?;
                if pos > 0 {
                    file.seek(SeekFrom::Start(pos - 1))?;
                }
                Ok(())
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Cannot unread on this stream")),
        }
    }
    
    /// Get the accumulated string from a string output stream
    pub fn get_output_stream_string(&mut self, id: StreamId) -> Option<String> {
        match self.get_mut(id) {
            Some(Stream::StringOutputStream { buffer }) => {
                let result = buffer.clone();
                buffer.clear();
                Some(result)
            }
            _ => None,
        }
    }
    
    /// Check if stream is at end of file
    pub fn stream_eof(&mut self, id: StreamId) -> io::Result<bool> {
        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, position }) => {
                Ok(*position >= buffer.len())
            }
            Some(Stream::FileInputStream { reader, .. }) => {
                let buf = reader.fill_buf()?;
                Ok(buf.is_empty())
            }
            Some(Stream::FileIoStream { file, .. }) => {
                let pos = file.stream_position()?;
                let len = file.metadata()?.len();
                Ok(pos >= len)
            }
            _ => Ok(false),
        }
    }

    /// Snapshot remaining textual input without changing stream position.
    /// Used by the Lisp reader pipeline for stream-backed READ forms.
    pub fn read_remaining_text(&mut self, id: StreamId) -> io::Result<String> {
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.read_remaining_text(input);
        }

        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, position }) => {
                Ok(buffer.chars().skip(*position).collect())
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let pos = reader.stream_position()?;
                let mut out = String::new();
                reader.read_to_string(&mut out)?;
                reader.seek(SeekFrom::Start(pos))?;
                Ok(out)
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let pos = file.stream_position()?;
                let mut out = String::new();
                file.read_to_string(&mut out)?;
                file.seek(SeekFrom::Start(pos))?;
                Ok(out)
            }
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Stream does not support textual reading",
            )),
        }
    }

    /// Advance textual input cursor by a number of characters.
    /// For file streams this currently assumes single-byte text encoding.
    pub fn advance_text_chars(&mut self, id: StreamId, count: usize) -> io::Result<()> {
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.advance_text_chars(input, count);
        }

        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, position }) => {
                let len = buffer.chars().count();
                *position = position.saturating_add(count).min(len);
                Ok(())
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut buf = [0u8; 1];
                for _ in 0..count {
                    if reader.read(&mut buf)? == 0 {
                        break;
                    }
                }
                Ok(())
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Character {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a character input stream",
                    ));
                }
                let mut buf = [0u8; 1];
                for _ in 0..count {
                    if file.read(&mut buf)? == 0 {
                        break;
                    }
                }
                Ok(())
            }
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Stream does not support textual reading",
            )),
        }
    }
    
    /// Flush output stream
    pub fn finish_output(&mut self, id: StreamId) -> io::Result<()> {
        match self.get_mut(id) {
            Some(Stream::Stdout) => io::stdout().flush(),
            Some(Stream::Stderr) => io::stderr().flush(),
            Some(Stream::FileOutputStream { file, .. }) => file.flush(),
            Some(Stream::FileIoStream { file, .. }) => file.flush(),
            _ => Ok(()),
        }
    }

    pub fn force_output(&mut self, id: StreamId) -> io::Result<()> {
        self.finish_output(id)
    }

    pub fn clear_output(&mut self, id: StreamId) -> io::Result<()> {
        match self.get_mut(id) {
            Some(Stream::StringOutputStream { buffer }) => {
                buffer.clear();
                Ok(())
            }
            Some(Stream::Stdout)
            | Some(Stream::Stderr)
            | Some(Stream::FileOutputStream { .. })
            | Some(Stream::FileIoStream { .. })
            | Some(Stream::BroadcastStream { .. })
            | Some(Stream::TwoWayStream { .. })
            | Some(Stream::EchoStream { .. }) => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not an output stream")),
        }
    }

    pub fn read_byte(&mut self, id: StreamId) -> io::Result<Option<u8>> {
        if let Some((input, output)) = match self.get(id) {
            Some(Stream::EchoStream { input, output }) => Some((*input, *output)),
            _ => None,
        } {
            let b = self.read_byte(input)?;
            if let Some(v) = b {
                self.write_byte(output, v)?;
            }
            return Ok(b);
        }
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.read_byte(input);
        }

        match self.get_mut(id) {
            Some(Stream::Stdin) => {
                let mut b = [0u8; 1];
                match io::stdin().lock().read(&mut b) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(b[0])),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::FileInputStream { reader, element_type, .. }) => {
                if *element_type != StreamElementType::Byte {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a byte input stream",
                    ));
                }
                let mut b = [0u8; 1];
                match reader.read(&mut b) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(b[0])),
                    Err(e) => Err(e),
                }
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Byte {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a byte input stream",
                    ));
                }
                let mut b = [0u8; 1];
                match file.read(&mut b) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(b[0])),
                    Err(e) => Err(e),
                }
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not a byte input stream")),
        }
    }

    pub fn write_byte(&mut self, id: StreamId, byte: u8) -> io::Result<()> {
        if let Some(targets) = match self.get(id) {
            Some(Stream::BroadcastStream { targets }) => Some(targets.clone()),
            _ => None,
        } {
            for target in targets {
                self.write_byte(target, byte)?;
            }
            return Ok(());
        }
        if let Some(output) = match self.get(id) {
            Some(Stream::TwoWayStream { output, .. }) => Some(*output),
            Some(Stream::EchoStream { output, .. }) => Some(*output),
            _ => None,
        } {
            return self.write_byte(output, byte);
        }

        match self.get_mut(id) {
            Some(Stream::Stdout) => {
                io::stdout().write_all(&[byte])?;
                io::stdout().flush()
            }
            Some(Stream::Stderr) => {
                io::stderr().write_all(&[byte])?;
                io::stderr().flush()
            }
            Some(Stream::StringOutputStream { buffer }) => {
                buffer.push(byte as char);
                Ok(())
            }
            Some(Stream::FileOutputStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Byte {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a byte output stream",
                    ));
                }
                file.write_all(&[byte])
            }
            Some(Stream::FileIoStream { file, element_type, .. }) => {
                if *element_type != StreamElementType::Byte {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Not a byte output stream",
                    ));
                }
                file.write_all(&[byte])
            }
            _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Not a byte output stream")),
        }
    }

    pub fn file_position(&mut self, id: StreamId) -> io::Result<Option<u64>> {
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.file_position(input);
        }

        match self.get_mut(id) {
            Some(Stream::StringInputStream { position, .. }) => Ok(Some(*position as u64)),
            Some(Stream::StringOutputStream { buffer }) => Ok(Some(buffer.chars().count() as u64)),
            Some(Stream::FileInputStream { reader, .. }) => Ok(Some(reader.stream_position()?)),
            Some(Stream::FileOutputStream { file, .. }) => Ok(Some(file.stream_position()?)),
            Some(Stream::FileIoStream { file, .. }) => Ok(Some(file.stream_position()?)),
            _ => Ok(None),
        }
    }

    pub fn set_file_position(&mut self, id: StreamId, pos: u64) -> io::Result<bool> {
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.set_file_position(input, pos);
        }

        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, position }) => {
                let len = buffer.chars().count() as u64;
                if pos > len {
                    return Ok(false);
                }
                *position = pos as usize;
                Ok(true)
            }
            Some(Stream::StringOutputStream { buffer }) => {
                let len = buffer.chars().count() as u64;
                if pos > len {
                    return Ok(false);
                }
                Ok(true)
            }
            Some(Stream::FileInputStream { reader, .. }) => {
                reader.seek(SeekFrom::Start(pos))?;
                Ok(true)
            }
            Some(Stream::FileOutputStream { file, .. }) => {
                file.seek(SeekFrom::Start(pos))?;
                Ok(true)
            }
            Some(Stream::FileIoStream { file, .. }) => {
                file.seek(SeekFrom::Start(pos))?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub fn file_length(&mut self, id: StreamId) -> io::Result<Option<u64>> {
        if let Some(input) = match self.get(id) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            _ => None,
        } {
            return self.file_length(input);
        }

        match self.get_mut(id) {
            Some(Stream::StringInputStream { buffer, .. }) => Ok(Some(buffer.chars().count() as u64)),
            Some(Stream::StringOutputStream { buffer }) => Ok(Some(buffer.chars().count() as u64)),
            Some(Stream::FileInputStream { reader, .. }) => Ok(Some(reader.get_ref().metadata()?.len())),
            Some(Stream::FileOutputStream { file, .. }) => Ok(Some(file.metadata()?.len())),
            Some(Stream::FileIoStream { file, .. }) => Ok(Some(file.metadata()?.len())),
            _ => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_string_output_stream() {
        let mut mgr = StreamManager::new();
        let id = mgr.alloc(Stream::StringOutputStream { buffer: String::new() });
        
        mgr.write_string(id, "Hello, ").unwrap();
        mgr.write_string(id, "World!").unwrap();
        
        let result = mgr.get_output_stream_string(id);
        assert_eq!(result, Some("Hello, World!".to_string()));
    }
    
    #[test]
    fn test_string_input_stream() {
        let mut mgr = StreamManager::new();
        let id = mgr.alloc(Stream::StringInputStream {
            buffer: "Hello".to_string(),
            position: 0,
        });
        
        assert_eq!(mgr.read_char(id).unwrap(), Some('H'));
        assert_eq!(mgr.read_char(id).unwrap(), Some('e'));
        assert_eq!(mgr.read_char(id).unwrap(), Some('l'));
        assert_eq!(mgr.read_char(id).unwrap(), Some('l'));
        assert_eq!(mgr.read_char(id).unwrap(), Some('o'));
        assert_eq!(mgr.read_char(id).unwrap(), None);
    }
    
    #[test]
    fn test_fresh_line() {
        let mut mgr = StreamManager::new();
        let id = mgr.alloc(Stream::StringOutputStream { buffer: String::new() });
        
        // At column 0, fresh-line should not add newline
        assert_eq!(mgr.fresh_line(id).unwrap(), false);
        
        // Write something
        mgr.write_string(id, "Hello").unwrap();
        
        // Now fresh-line should add newline
        assert_eq!(mgr.fresh_line(id).unwrap(), true);
        
        // Now at column 0 again
        assert_eq!(mgr.fresh_line(id).unwrap(), false);
        
        let result = mgr.get_output_stream_string(id);
        assert_eq!(result, Some("Hello\n".to_string()));
    }
}
