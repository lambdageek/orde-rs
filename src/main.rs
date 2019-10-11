mod stlc;

fn compute () {
    use stlc::Var;
    let x = Var::Local(0);
    println!("is_local (x) => {}", &x.is_local ());
}

fn main() {
    println!("Hello, world!");
    compute ();
}
