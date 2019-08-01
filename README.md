# OsStrOps

Some basic string operations on OsStr.

On Unix, this always operates on bytes, on Windows it tries to operate on `str`,
but will fall back on `Vec<u16>` using encode/decode_wide() if necessary.

```rust
use osstrops::OsStrOps;

fn main() -> std::io::Result<()> {
    for arg in std::env::args_os() {
        let argop = OsStrOps::from(&arg);

        if argop.starts_with("--path=") {
            if let (_, Some(path)) = argop.split_at_byte(b'=') {
                println!("Path: {}", path.to_string_lossy());
                let _file = std::fs::File::open(path)?;
            }
        }
    }

    Ok(())
}
```
