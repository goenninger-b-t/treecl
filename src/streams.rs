// TreeCL Streams - ANSI CL I/O Abstraction
//
// Implements stream types for input/output operations.

use std::io::{self, Read, Write, BufRead, BufReader};
use std::fs::File;

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
    },
    FileInputStream {
        path: String,
        reader: BufReader<File>,
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
        if id.0 <= 2 {
            return false; // Can't close standard streams
        }
        if let Some(slot) = self.streams.get_mut(id.0 as usize) {
            if slot.is_some() {
                *slot = None;
                self.free_list.push(id.0);
                self.column_positions.remove(&id.0);
                return true;
            }
        }
        false
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
            Some(Stream::FileOutputStream { file, .. }) => {
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
            Some(Stream::FileInputStream { reader, .. }) => {
                let mut buf = [0u8; 1];
                match reader.read(&mut buf) {
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
            Some(Stream::FileInputStream { reader, .. }) => {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) => Ok(None),
                    Ok(_) => Ok(Some(line)),
                    Err(e) => Err(e),
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
            Some(Stream::FileInputStream { reader, .. }) => {
                let buf = reader.fill_buf()?;
                if buf.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(buf[0] as char))
                }
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
            _ => Ok(false),
        }
    }
    
    /// Flush output stream
    pub fn finish_output(&mut self, id: StreamId) -> io::Result<()> {
        match self.get_mut(id) {
            Some(Stream::Stdout) => io::stdout().flush(),
            Some(Stream::Stderr) => io::stderr().flush(),
            Some(Stream::FileOutputStream { file, .. }) => file.flush(),
            _ => Ok(()),
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
