use std::ffi::OsStr;

/// An OsStr extension trait that assumes UTF-8 or WTF-8 (or similar)
pub trait OsStrExt {
    fn starts_with<S: AsRef<[u8]>>(&self, s: S) -> bool;
    fn starts_with_osstr<S: AsRef<OsStr>>(&self, s: S) -> bool;
    fn split_at_byte(&self, b: u8) -> (&OsStr, Option<&OsStr>);
    fn len_bytes(&self) -> usize;
    fn split_at(&self, i: usize) -> (&OsStr, &OsStr);
    fn trim_start_matches(&self, b: u8) -> &OsStr;
    fn contains_byte(&self, b: u8) -> bool;
    fn split(&self, b: u8) -> OsSplit;
}

impl OsStrExt for OsStr {
    fn starts_with<S: AsRef<[u8]>>(&self, s: S) -> bool {
        os_str_as_u8_slice(&self).starts_with(s.as_ref())
    }

    fn starts_with_osstr<S: AsRef<OsStr>>(&self, s: S) -> bool {
        os_str_as_u8_slice(&self).starts_with(os_str_as_u8_slice(s.as_ref()))
    }

    fn len_bytes(&self) -> usize {
        os_str_as_u8_slice(&self).len()
    }

    /// Panics if self[i] is not a codepoint boundary, or is out of bounds
    fn split_at(&self, i: usize) -> (&OsStr, &OsStr) {
        let slice = os_str_as_u8_slice(&self);

        assert!(slice[i] & 0xc0 != 0x80);

        unsafe {
            (
                u8_slice_as_os_str(&slice[..i]),
                u8_slice_as_os_str(&slice[i..]),
            )
        }
    }

    /// Panics if byte is > 127
    fn split_at_byte(&self, b: u8) -> (&OsStr, Option<&OsStr>) {
        assert!(b <= 127);

        unsafe {
            let mut iter = os_str_as_u8_slice(&self).splitn(2, |h| *h == b);
            let before = iter.next();
            let after = iter.next();

            (
                before.map(|s| u8_slice_as_os_str(s)).expect("splitn"),
                after.map(|s| u8_slice_as_os_str(s)),
            )
        }
    }

    fn contains_byte(&self, byte: u8) -> bool {
        os_str_as_u8_slice(&self).iter().copied().any(|b| b == byte)
    }

    /// Panics if byte is > 127
    fn trim_start_matches(&self, byte: u8) -> &OsStr {
        assert!(byte <= 127);

        let bytes = os_str_as_u8_slice(&self);

        match bytes.iter().copied().position(|b| b != byte) {
            Some(0) => &self,
            Some(pos) => unsafe { u8_slice_as_os_str(&bytes[pos..]) },
            None => unsafe { u8_slice_as_os_str(&bytes[bytes.len()..]) },
        }
    }

    /// Panics of sep is > 127
    fn split(&self, b: u8) -> OsSplit {
        assert!(b <= 127);

        OsSplit {
            sep: b,
            val: os_str_as_u8_slice(&self),
            pos: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct OsSplit<'a> {
    sep: u8,
    val: &'a [u8],
    pos: usize,
}

impl<'a> Iterator for OsSplit<'a> {
    type Item = &'a OsStr;

    fn next(&mut self) -> Option<&'a OsStr> {
        if self.pos == self.val.len() {
            return None;
        }

        let start = self.pos;

        for b in &self.val[start..] {
            self.pos += 1;
            if *b == self.sep {
                return Some(unsafe { u8_slice_as_os_str(&self.val[start..self.pos - 1]) });
            }
        }

        Some(unsafe { u8_slice_as_os_str(&self.val[start..]) })
    }
}

fn os_str_as_u8_slice(s: &OsStr) -> &[u8] {
    unsafe { &*(s as *const OsStr as *const [u8]) }
}

unsafe fn u8_slice_as_os_str(s: &[u8]) -> &OsStr {
    &*(s as *const [u8] as *const OsStr)
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ffi::OsString;

    #[test]
    fn test_starts_with() {
        let x = OsString::from("foo bar baz moop");

        assert!(x.starts_with("foo bar"));
        assert!(!x.starts_with("oo bar"));

        assert!(x.starts_with_osstr(&x));
        assert!(!x.starts_with_osstr(&OsString::from("oo bar")));
    }

    #[test]
    fn test_split_at() {
        let x = OsString::from("foo bar baz");

        let y = x.split_at(6);
        assert_eq!(y.0, OsString::from("foo ba"));
        assert_eq!(y.1, OsString::from("r baz"));
    }

    #[test]
    fn test_split_at_byte() {
        let x = OsString::from("foo=bar");
        let y = x.split_at_byte(b'=');
        assert_eq!(y.0, OsString::from("foo"));
        assert_eq!(y.1.unwrap(), OsString::from("bar"));

        let x = OsString::from("foobar");
        let y = x.split_at_byte(b'=');
        assert_eq!(y.0, OsString::from("foobar"));
        assert!(y.1.is_none());
    }

    #[test]
    fn test_trim_start_matches() {
        let x = OsString::from("--foo");
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from("foo"));

        let x = OsString::from("foo");
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from("foo"));

        let x = OsString::from("----");
        let y = x.trim_start_matches(b'-');
        assert_eq!(y, OsString::from(""));
    }

    #[test]
    fn test_split() {
        let x = OsString::from("foo/bar/baz");
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
