use std::collections::{HashMap};
fn main() {
    let sequence = vec![1,2,3,4,1,2,5,6];
    let mut adjacency_list = HashMap::new();
    let mut res = Vec::new();
    let sequences_len = sequence.len();
    let mut index_map = HashMap::new();
    
    adjacency_list.insert(1,vec![2]);
    adjacency_list.insert(2,vec![3, 4]);
    adjacency_list.insert(3,vec![4]);
    adjacency_list.insert(5,vec![6]);

    for i in 0..sequences_len {
        let func = sequence[i];
        let adjacency_list_len = adjacency_list.get(&func).unwrap().len();
        if adjacency_list_len != 1{
            res.push(func);
            index_map.insert(i, res.len());
        }else{
            let mut index = 0;
            for j in 0..adjacency_list_len{
                if sequence[index] == func{
                    if j == 1{ 
                        res.push(func);
                    }else{
                        res.push(func*10);
                    }
                    index_map.insert(index, res.len());
                    index = index + 1;
                }
            }
        }
    }
    println!("{:?}", res);
    println!("{:?}", index_map);
}
