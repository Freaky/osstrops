use std::borrow::Cow;
use std::ffi::{OsString, OsStr};
use std::str;

#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;

#[cfg(windows)]
use std::os::windows::ffi::{OsStrExt, OsStringExt};

#[derive(Debug, Clone)]
pub enum OsStrOps<'a> {
    #[cfg(not(unix))]
    Str(&'a str), // can be represented as UTF-8, just delegate
    #[cfg(unix)]
    Bytes(&'a [u8]), // Unix - can work on the raw bytes safely
    #[cfg(windows)]
    Wide(Vec<u16>), // Windows - invalid UTF-8, work on wide chars
}

impl<'a, T: ?Sized + AsRef<OsStr>> From<&'a T> for OsStrOps<'a> {
    fn from(s: &'a T) -> Self {
        let s = s.as_ref();

        #[cfg(unix)]
        return OsStrOps::Bytes(s.as_bytes());

        #[cfg(not(unix))]
        {
            if let Some(utf8) = s.to_str() {
                return OsStrOps::Str(utf8);
            }
        }

        #[cfg(windows)]
        return OsStrOps::Wide(s.encode_wide().collect());

        #[cfg(not(any(windows, unix)))]
        panic!("Non-Unicode OsString on unsupported platform");
    }
}

impl OsStrOps<'_> {
    pub fn as_str_lossy(&self) -> Cow<str> {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => Cow::Borrowed(v),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => String::from_utf8_lossy(&v),
            #[cfg(windows)]
            OsStrOps::Wide(v) => Cow::Owned(OsString::from_wide(v).to_string_lossy().into_owned()),
        }
    }

    pub fn as_bytes_lossy(&self) -> Cow<[u8]> {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => Cow::Borrowed(v.as_bytes()),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => Cow::Borrowed(&v),
            #[cfg(windows)]
            OsStrOps::Wide(v) => Cow::Owned(OsString::from_wide(v).to_string_lossy().into_owned().into_bytes()),
        }
    }

    pub fn into_os_string(self) -> OsString {
        match self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => OsString::from(v),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => OsStr::from_bytes(v).to_os_string(),
            #[cfg(windows)]
            OsStrOps::Wide(v) => OsString::from_wide(&v)
        }
    }

    pub fn starts_with<S: AsRef<str>>(&self, s: S) -> bool {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => v.starts_with(s.as_ref()),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => v.starts_with(s.as_ref().as_bytes()),
            #[cfg(windows)]
            OsStrOps::Wide(v) => v.starts_with(&s.as_ref().encode_utf16().collect::<Vec<u16>>()),
        }
    }

    pub fn contains_byte(&self, b: u8) -> bool {
        assert!(b <= 127);

        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => v.contains(b as char),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => v.contains(&b),
            #[cfg(windows)]
            OsStrOps::Wide(v) => v.contains(&u16::from(b)),
        }
    }

    pub fn split_at_byte(&self, b: u8) -> (Cow<OsStr>, Option<Cow<OsStr>>) {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => {
                let c = b as char;
                let mut iter = v.splitn(2, |n| n == c);
                let before = iter.next();
                let after = iter.next();

                (
                    before.map(|s| Cow::Borrowed(s.as_ref())).unwrap(),
                    after.map(|s| Cow::Borrowed(s.as_ref())),
                )
            }
            #[cfg(unix)]
            OsStrOps::Bytes(v) => {
                let mut iter = v.splitn(2, |n| *n == b);
                let before = iter.next();
                let after = iter.next();

                (
                    before.map(|s| Cow::Borrowed(OsStr::from_bytes(s))).unwrap(),
                    after.map(|s| Cow::Borrowed(OsStr::from_bytes(s))),
                )
            }
            #[cfg(windows)]
            OsStrOps::Wide(v) => {
                assert!(b <= 127);

                let mut iter = v.splitn(2, |n| *n == u16::from(b));
                let before = iter.next();
                let after = iter.next();

                (
                    before.map(|s| Cow::Owned(OsString::from_wide(s))).unwrap(),
                    after.map(|s| Cow::Owned(OsString::from_wide(s))),
                )
            }
        }
    }

    pub fn len(&self) -> usize {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => v.len(),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => v.len(),
            #[cfg(windows)]
            OsStrOps::Wide(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn split_at(&self, i: usize) -> (Cow<OsStr>, Cow<OsStr>) {
        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => {
                let bits = v.split_at(i);
                (
                    Cow::Borrowed(bits.0.as_ref()),
                    Cow::Borrowed(bits.1.as_ref()),
                )
            }
            #[cfg(unix)]
            OsStrOps::Bytes(v) => {
                let bits = v.split_at(i);
                (
                    Cow::Borrowed(OsStr::from_bytes(bits.0)),
                    Cow::Borrowed(OsStr::from_bytes(bits.1)),
                )
            }
            #[cfg(windows)]
            OsStrOps::Wide(v) => {
                let bits = v.split_at(i);
                (
                    Cow::Owned(OsString::from_wide(bits.0)),
                    Cow::Owned(OsString::from_wide(bits.1)),
                )
            }
        }
    }

    pub fn trim_start_matches(&self, b: u8) -> Cow<OsStr> {
        assert!(b <= 127);

        match &self {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => Cow::Borrowed(v.trim_start_matches(b as char).as_ref()),
            #[cfg(unix)]
            OsStrOps::Bytes(v) => match v.iter().copied().position(|n| n != b) {
                Some(0) => Cow::Borrowed(OsStr::from_bytes(v)),
                Some(pos) => Cow::Borrowed(OsStr::from_bytes(&v[pos..])),
                None => Cow::Borrowed(OsStr::from_bytes(&v[v.len()..])),
            },
            #[cfg(windows)]
            OsStrOps::Wide(v) => match v.iter().copied().position(|n| n != u16::from(b)) {
                Some(0) => Cow::Owned(OsString::from_wide(v)),
                Some(pos) => Cow::Owned(OsString::from_wide(&v[pos..])),
                None => Cow::Owned(OsString::from_wide(&v[v.len()..])),
            },
        }
    }

    pub fn split(&self, b: u8) -> OsSplit {
        assert!(b <= 127);

        OsSplit {
            sep: b,
            val: &self,
            pos: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct OsSplit<'a> {
    sep: u8,
    val: &'a OsStrOps<'a>,
    pos: usize,
}

impl<'a> Iterator for OsSplit<'a> {
    type Item = Cow<'a, OsStr>;

    fn next(&mut self) -> Option<Cow<'a, OsStr>> {
        if self.pos == self.val.len() {
            return None;
        }

        let start = self.pos;

        match &self.val {
            #[cfg(not(unix))]
            OsStrOps::Str(v) => {
                for b in &v.as_bytes()[start..] {
                    self.pos += 1;
                    // This is safe because sep is asserted < 128 in split()
                    if *b == self.sep {
                        return Some(Cow::Borrowed(v[start..self.pos - 1].as_ref()));
                    }
                }

                Some(Cow::Borrowed(v[start..].as_ref()))
            }
            #[cfg(unix)]
            OsStrOps::Bytes(v) => {
                for b in &v[start..] {
                    self.pos += 1;
                    if *b == self.sep {
                        return Some(Cow::Borrowed(OsStr::from_bytes(&v[start..self.pos - 1])));
                    }
                }

                Some(Cow::Borrowed(OsStr::from_bytes(&v[start..])))
            }
            #[cfg(windows)]
            OsStrOps::Wide(v) => {
                for b in &v[start..] {
                    self.pos += 1;
                    if *b == u16::from(self.sep) {
                        return Some(Cow::Owned(OsString::from_wide(&v[start..self.pos - 1])));
                    }
                }

                Some(Cow::Owned(OsString::from_wide(&v[start..])))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::OsString;

    #[test]
    fn test_starts_with() {
        let s = OsString::from("foo bar baz moop");
        let x = OsStrOps::from(&s);

        assert!(x.starts_with("foo bar"));
        assert!(!x.starts_with("oo bar"));
    }

    #[test]
    fn test_contains_byte() {
        let s = OsString::from("foo=bar");
        let x = OsStrOps::from(&s);

        assert!(x.contains_byte(b'='));
        assert!(!x.contains_byte(b'z'));
    }

    #[test]
    fn test_split_at() {
        let s = OsString::from("foo=bar");
        let x = OsStrOps::from(&s);
        let y = x.split_at(4);
        assert_eq!(y.0, OsString::from("foo="));
        assert_eq!(y.1, OsString::from("bar"));
    }

    #[test]
    fn test_split_at_byte() {
        let s = OsString::from("foo=bar");
        let x = OsStrOps::from(&s);
        let y = x.split_at_byte(b'=');
        assert_eq!(y.0, OsString::from("foo"));
        assert_eq!(y.1.unwrap(), OsString::from("bar"));

        let s = OsString::from("foobar");
        let x = OsStrOps::from(&s);
        let y = x.split_at_byte(b'=');
        assert_eq!(y.0, OsString::from("foobar"));
        assert!(y.1.is_none());
    }

    #[test]
    fn test_trim_start_matches() {
        let s = OsString::from("--foo");
        let x = OsStrOps::from(&s);
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from("foo"));

        let s = OsString::from("foo");
        let x = OsStrOps::from(&s);
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from("foo"));

        let s = OsString::from("----");
        let x = OsStrOps::from(&s);
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from(""));
    }

    #[test]
    fn test_split() {
        let s = OsString::from("foo/bar/baz");
        let x = OsStrOps::from(&s);
        let y: Vec<_> = x.split(b'/').collect();

        assert_eq!(
            vec![
                OsString::from("foo"),
                OsString::from("bar"),
                OsString::from("baz")
            ],
            y
        );
    }
}
