use url::Host;

#[macro_use]
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

#[derive(Eq, PartialEq, Debug)]
struct Ret{
    field0: bool,
    field1: Host<String>
}


fn test_function0_1(_param0 :& str ,_param1 :& str) -> Ret{
    let _local0 = url::Url::parse(_param0);
    let _local1 = url::Url::parse(_param1);
    let _local2_param0_helper1 = _unwrap_result(_local0);
    let ret0 = url::Url::host(&(_local2_param0_helper1));
    let ret0 = ret0.unwrap().to_owned();
    let _local3_param0_helper1 = _unwrap_result(_local1);
    let ret1 = url::Url::has_host(&(_local3_param0_helper1));
    Ret{field0:ret1, field1:ret0}
}


fn test_function0_0(_param0 :& str ,_param1 :& str) ->Ret{
    let _local0 = url::Url::parse(_param0);
    let _local1 = url::Url::parse(_param1);
    let _local2_param0_helper1 = _unwrap_result(_local0);
    let ret0 = url::Url::has_host(&(_local2_param0_helper1));
    let _local3_param0_helper1 = _unwrap_result(_local1);
    let ret1 = url::Url::host(&(_local3_param0_helper1));
    let ret1 = ret1.unwrap().to_owned();
    Ret{field0:ret0, field1:ret1}
}

fn main() {
    let mut _param0 = "";
    let _param1 = "";
    let ret0 = test_function0_0(_param0 ,_param1);
    let ret1 = test_function0_1(_param0 ,_param1);
    assert_eq!(ret0, ret1);
}