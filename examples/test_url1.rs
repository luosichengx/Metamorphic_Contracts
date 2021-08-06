// #[macro_use]
// extern crate verification_annotations as verifier;
extern crate url;
fn _unwrap_result<T, E>(_res: Result<T, E>) -> T {
    match _res {
        Ok(_t) => _t,
        Err(_) => {
            use std::process;
            process::exit(0);
        },
    }
}


fn test_function0(_param0 :&str ,_param1 :&str) {
    let _local0_0 = url::Url::parse(_param0);
    let _local1_0 = url::Url::parse(_param1);
    let _local2_param0_helper1_0 = _unwrap_result(_local0_0);
    let ret0_0 = url::Url::has_host(&(_local2_param0_helper1_0));
    let _local3_param0_helper1_0 = _unwrap_result(_local1_0);
    let ret1_0 = url::Url::host(&(_local3_param0_helper1_0));
    let _local0_1 = url::Url::parse(_param0);
    let _local1_1 = url::Url::parse(_param1);
    let _local2_param0_helper1_1 = _unwrap_result(_local0_1);
    let ret0_1 = url::Url::host(&(_local2_param0_helper1_1));
    let _local3_param0_helper1_1 = _unwrap_result(_local1_1);
    let ret1_1 = url::Url::has_host(&(_local3_param0_helper1_1));
    assert_eq!(ret0_0, ret1_1);
    assert_eq!(ret1_0, ret0_1);
}

fn main() {
    // let a0:u8 = verifier::AbstractValue::abstract_value();
    // verifier::assume(0 <= a0 && a0 < 6);
    // let mut b0 = Vec::new();
    // for _ in 0..a0{
    //     let c = verifier::AbstractValue::abstract_value();
    //     verifier::assume(32 <= c && c < 128);
    //     b0.push(c);
    // }
    // let d0 = std::str::from_utf8(&b0);
    // let _param0 = _unwrap_result(d0);
    // let a1:u8 = verifier::AbstractValue::abstract_value();
    // verifier::assume(0 <= a1 && a1 < 6);
    // let mut b1 = Vec::new();
    // for _ in 0..a1{
    //     let c = verifier::AbstractValue::abstract_value();
    //     verifier::assume(32 <= c && c < 128);
    //     b1.push(c);
    // }
    // let d1 = std::str::from_utf8(&b1);
    // let _param1 = _unwrap_result(d1);
    let _param0 = "";
    let _param1 = "";
    test_function0(_param0 ,_param1);
}
