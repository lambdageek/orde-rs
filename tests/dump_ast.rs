use orde_rs::stlc;

#[test]
fn dump_var () {
    let v0 = stlc::Var::Local (0);
    assert_eq! (format!("{:?}", v0), "Local(0)");
    
}
