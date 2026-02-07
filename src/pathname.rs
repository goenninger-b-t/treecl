#[derive(Clone, Debug, PartialEq)]
pub struct PathnameDirectory {
    pub absolute: bool,
    pub components: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Pathname {
    pub namestring: String,
    pub host: Option<String>,
    pub device: Option<String>,
    pub directory: Option<PathnameDirectory>,
    pub name: Option<String>,
    pub type_: Option<String>,
    pub version: Option<String>,
}

impl Pathname {
    pub fn has_logical_syntax(raw: &str) -> bool {
        let trimmed = raw.trim();
        if trimmed.contains(';') {
            return true;
        }

        let bytes = trimmed.as_bytes();
        let colon_idx = trimmed.find(':');
        let sep_idx = trimmed.find(|c| c == '/' || c == '\\');
        let is_drive = colon_idx == Some(1)
            && bytes
                .first()
                .is_some_and(|b| b.is_ascii_alphabetic());
        colon_idx.is_some()
            && !is_drive
            && (sep_idx.is_none() || colon_idx.unwrap() < sep_idx.unwrap())
    }

    pub fn from_namestring(raw: &str) -> Self {
        let namestring = raw.to_string();
        let trimmed = raw.trim();

        let mut host: Option<String> = None;
        let mut device: Option<String> = None;
        let mut directory: Option<PathnameDirectory> = None;
        let mut name: Option<String> = None;
        let mut type_: Option<String> = None;
        let mut version: Option<String> = None;

        let bytes = trimmed.as_bytes();
        if bytes.len() >= 2 && bytes[1] == b':' && bytes[0].is_ascii_alphabetic() {
            device = Some((bytes[0] as char).to_string());
        }

        let colon_idx = trimmed.find(':');
        let logical = Self::has_logical_syntax(trimmed);

        if logical {
            let rest = if let Some(idx) = colon_idx {
                let host_part = trimmed[..idx].trim();
                if !host_part.is_empty() {
                    host = Some(host_part.to_string());
                }
                &trimmed[idx + 1..]
            } else {
                trimmed
            };
            let mut segments: Vec<&str> = rest.split(';').collect();
            let ends_with_sep = rest.ends_with(';');
            let file_part = if ends_with_sep {
                None
            } else {
                segments.pop().filter(|s| !s.is_empty())
            };

            let mut components: Vec<String> = Vec::new();
            for seg in segments {
                if seg.is_empty() {
                    continue;
                }
                components.push(seg.to_string());
            }
            let absolute = rest.starts_with(';');
            if !components.is_empty() || absolute {
                directory = Some(PathnameDirectory { absolute, components });
            }

            if let Some(file) = file_part {
                let fields: Vec<&str> = file.split('.').collect();
                match fields.len() {
                    0 => {}
                    1 => {
                        if !fields[0].is_empty() {
                            name = Some(fields[0].to_string());
                        }
                    }
                    2 => {
                        if !fields[0].is_empty() {
                            name = Some(fields[0].to_string());
                        }
                        if !fields[1].is_empty() {
                            type_ = Some(fields[1].to_string());
                        }
                    }
                    _ => {
                        if !fields[0].is_empty() {
                            name = Some(fields[0].to_string());
                        }
                        if !fields[1].is_empty() {
                            type_ = Some(fields[1].to_string());
                        }
                        let version_text = fields[2..].join(".");
                        if !version_text.is_empty() {
                            version = Some(version_text);
                        }
                    }
                }
            }
        } else {
            let has_trailing_sep =
                trimmed.ends_with(std::path::MAIN_SEPARATOR) || trimmed.ends_with('/');
            let path = std::path::Path::new(trimmed);

            let file_name = if has_trailing_sep { None } else { path.file_name() };
            name = file_name
                .and_then(|f| std::path::Path::new(f).file_stem())
                .map(|s| s.to_string_lossy().to_string());
            type_ = file_name
                .and_then(|f| std::path::Path::new(f).extension())
                .map(|s| s.to_string_lossy().to_string());

            let dir_path = if has_trailing_sep {
                path
            } else {
                path.parent().unwrap_or_else(|| std::path::Path::new(""))
            };

            let mut components: Vec<String> = Vec::new();
            let mut absolute = false;
            for comp in dir_path.components() {
                match comp {
                    std::path::Component::RootDir => {
                        absolute = true;
                    }
                    std::path::Component::CurDir => components.push(".".to_string()),
                    std::path::Component::ParentDir => components.push("..".to_string()),
                    std::path::Component::Normal(s) => {
                        components.push(s.to_string_lossy().to_string());
                    }
                    std::path::Component::Prefix(prefix) => {
                        absolute = true;
                        components.push(prefix.as_os_str().to_string_lossy().to_string());
                    }
                }
            }

            if !components.is_empty() || absolute {
                directory = Some(PathnameDirectory { absolute, components });
            }
        }

        Self {
            namestring,
            host,
            device,
            directory,
            name,
            type_,
            version,
        }
    }

    pub fn namestring(&self) -> &str {
        &self.namestring
    }
}
