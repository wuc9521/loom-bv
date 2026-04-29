use std::path::PathBuf;

fn main() {
    let dir: PathBuf = ["tree-sitter", "tree-sitter-python"].iter().collect();

    let mut python_parser = cc::Build::new();
    python_parser
        .include(&dir)
        .file(dir.join("parser.c"))
        .warnings(false)
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-unused-parameter");
    python_parser.compile("tree-sitter-python");
    let mut python_scanner = cc::Build::new();
    python_scanner
        .cpp(true)
        .include(&dir)
        .file(dir.join("scanner.cc"))
        .warnings(false)
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-unused-parameter");
    python_scanner.compile("tree-sitter-python-scanner");

    let dir2: PathBuf = ["tree-sitter", "tree-sitter-markdown"].iter().collect();

    let mut markdown = cc::Build::new();
    markdown
        .include(&dir2)
        .file(dir2.join("parser.c"))
        .file(dir2.join("scanner.cc"))
        .warnings(false)
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-unused-parameter");
    markdown.compile("tree-sitter-markdown");
}
