//! Temporary stack probe.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let name = args[1].clone();
    let kb: usize = args[2].parse().unwrap();
    let n = 5000;
    let src = match name.as_str() {
        "paren" => format!("fn f() {{ {}x{} }}", "(".repeat(n), ")".repeat(n)),
        "brack" => format!("fn f() {{ {}x{} }}", "[".repeat(n), "]".repeat(n)),
        "brace" => format!("fn f() {{ {}x{} }}", "{".repeat(n), "}".repeat(n)),
        "closure" => format!("fn f() {{ {}x }}", "|| ".repeat(n)),
        "if" => format!("fn f() {{ {}x{} }}", "if a { ".repeat(n), " }".repeat(n)),
        "call" => format!("fn f() {{ {}x{} }}", "f(".repeat(n), ")".repeat(n)),
        "str" => format!("fn f() {{ {}x{} }}", "\"{".repeat(2000), "}\"".repeat(2000)),
        "tyref" => format!("fn f(x: {}T) {{}}", "&".repeat(n)),
        "typar" => format!("fn f(x: {}T{}) {{}}", "(".repeat(n), ")".repeat(n)),
        "tyvec" => format!("fn f(x: {}T{}) {{}}", "Vec<".repeat(n), ">".repeat(n)),
        "pat" => format!("fn f() {{ let {}x{} = 1 }}", "(".repeat(n), ")".repeat(n)),
        "mod" => format!("{}{}", "mod m { ".repeat(n), "}".repeat(n)),
        "chain" => format!("fn f() {{ x{} }}", " + x".repeat(100_000)),
        "neg" => format!("fn f() {{ {}x }}", "-".repeat(100_000)),
        _ => panic!(),
    };
    let r = std::thread::Builder::new().stack_size(kb * 1024)
        .spawn(move || weft_syntax::parse_file(&src).err().map(|e| e.message)).unwrap().join().unwrap();
    println!("{r:?}");
}
