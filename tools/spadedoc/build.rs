use std::{env, fs, io, path::PathBuf, process::Command};

fn grab(url: &str, path: &str) -> io::Result<()> {
    println!("Loading {url} as {path}");

    let highlight_js = Command::new("curl").arg(url).output()?;

    let as_text = String::from_utf8(highlight_js.stdout).map_err(io::Error::other)?;

    fs::write(
        PathBuf::from(env::var("OUT_DIR").expect("in build script")).join(path),
        as_text,
    )?;

    println!(" Loaded {url} as {path}");

    Ok(())
}

fn main() -> io::Result<()> {
    // pass -vv to see these

    println!("Grabbing assets");
    grab(
        "https://gitlab.com/spade-lang/book/-/raw/main/src/spade-highlight.js?ref_type=heads",
        "spade-highlight.js",
    )?;
    grab(
        "https://gitlab.com/spade-lang/book/-/raw/main/src/custom-highlight.css?ref_type=heads",
        "spade-theme.css",
    )?;
    println!(" Grabbed assets");

    Ok(())
}
