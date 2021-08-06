/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use proc_macro2::{Ident, Punct, Span, TokenStream};
use quote::ToTokens;
use syn::{
    spanned::Spanned, visit_mut as visitor, Attribute, Expr, ExprCall,
    ReturnType, FnArg, PatType, Pat
};

use crate::implementation::{
    Contract, ContractMode, ContractType, FuncWithContracts,
};
use std::collections::HashMap;

/// Substitution for `old()` expressions.
pub(crate) struct OldExpr {
    /// Name of the variable binder.
    pub(crate) name: String,
    /// Expression to be evaluated.
    pub(crate) expr: Expr,
}

#[derive(Debug)]
pub struct MRRunInfo {
    /// index of the variable binder.
    pub index: usize,
    /// index of return number.
    pub retindex1: usize,
    pub retindex2: usize,
    /// mr relation
    mr:ContractType,
    pub variable: Ident,
    pub variable_name: String,
    pub change: TokenStream,
}

impl MRRunInfo{
    fn new(index: usize, retindex1: usize, retindex2: usize, mr:ContractType, variable: Ident, variable_name: String, change: TokenStream)->Self{
        MRRunInfo{
            index,
            retindex1,
            retindex2,
            mr,
            variable,
            variable_name,
            change,
        }
    }
}

/// Extract calls to the pseudo-function `old()` in post-conditions,
/// which evaluates an expression in a context *before* the
/// to-be-checked-function is executed.
pub(crate) fn extract_old_calls(contracts: &mut [Contract]) -> Vec<OldExpr> {
    struct OldExtractor {
        last_id: usize,
        olds: Vec<OldExpr>,
    }

    // if the call is a call to old() then the argument will be
    // returned.
    fn get_old_data(call: &ExprCall) -> Option<Expr> {
        // must have only one argument
        if call.args.len() != 1 {
            return None;
        }

        if let Expr::Path(path) = &*call.func {
            if path.path.is_ident("old") {
                Some(call.args[0].clone())
            } else {
                None
            }
        } else {
            None
        }
    }

    impl visitor::VisitMut for OldExtractor {
        fn visit_expr_mut(&mut self, expr: &mut Expr) {
            if let Expr::Call(call) = expr {
                if let Some(mut old_arg) = get_old_data(call) {
                    // if it's a call to old() then add to list of
                    // old expressions and continue to check the
                    // argument.

                    self.visit_expr_mut(&mut old_arg);

                    let id = self.last_id;
                    self.last_id += 1;

                    let old_var_name = format!("__contract_old_{}", id);

                    let old_expr = OldExpr {
                        name: old_var_name.clone(),
                        expr: old_arg,
                    };

                    self.olds.push(old_expr);

                    // override the original expression with the new variable
                    // identifier
                    *expr = {
                        let span = expr.span();

                        let ident = syn::Ident::new(&old_var_name, span);

                        let toks = quote::quote_spanned! { span=> #ident };

                        syn::parse(toks.into()).unwrap()
                    };
                } else {
                    // otherwise continue visiting the expression call
                    visitor::visit_expr_call_mut(self, call);
                }
            } else {
                visitor::visit_expr_mut(self, expr);
            }
        }
    }

    let mut extractor = OldExtractor {
        last_id: 0,
        olds: vec![],
    };

    for contract in contracts {
        if contract.ty != ContractType::Ensures {
            continue;
        }

        for assertion in &mut contract.assertions {
            use visitor::VisitMut;
            extractor.visit_expr_mut(assertion);
        }
    }

    extractor.olds
}

fn get_assert_macro(
    ctype: ContractType, // only Pre/Post allowed.
    mode: ContractMode,
    span: Span,
) -> Option<Ident> {
    if cfg!(feature = "mirai_assertions") {
        match (ctype, mode) {
            (ContractType::Requires, ContractMode::Always) => {
                Some(Ident::new("checked_precondition", span))
            }
            (ContractType::Requires, ContractMode::Debug) => {
                Some(Ident::new("debug_checked_precondition", span))
            }
            (ContractType::Requires, ContractMode::Test) => {
                Some(Ident::new("debug_checked_precondition", span))
            }
            (ContractType::Requires, ContractMode::Disabled) => {
                Some(Ident::new("precondition", span))
            }
            (ContractType::Requires, ContractMode::LogOnly) => {
                Some(Ident::new("precondition", span))
            }
            (ContractType::Ensures, ContractMode::Always) => {
                Some(Ident::new("checked_postcondition", span))
            }
            (ContractType::Ensures, ContractMode::Debug) => {
                Some(Ident::new("debug_checked_postcondition", span))
            }
            (ContractType::Ensures, ContractMode::Test) => {
                Some(Ident::new("debug_checked_postcondition", span))
            }
            (ContractType::Ensures, ContractMode::Disabled) => {
                Some(Ident::new("postcondition", span))
            }
            (ContractType::Ensures, ContractMode::LogOnly) => {
                Some(Ident::new("postcondition", span))
            }
            (ContractType::Invariant, _) => {
                panic!("expected Invariant to be narrowed down to Pre/Post")
            }
            (ContractType::Cyclicity, _) => {
                Some(Ident::new("check_add_equal", span))
            }
            (ContractType::AddNotEqual, _) => {
                Some(Ident::new("check_add_not_equal", span))
            }
            (ContractType::LocalInvariance, _) => {
                Some(Ident::new("local_invariance", span))
            }
            (ContractType::Monotonicity, _) => {
                Some(Ident::new("monotonicity", span))
            }
            (ContractType::Symmetry, _) => {
                Some(Ident::new("symmetry", span))
            }
            (ContractType::Homomorphism, _) => {
                Some(Ident::new("homomorphism", span))
            }
            (ContractType::IterConsistency, _) => {
                Some(Ident::new("iter_consistency", span))
            }
        }
    } else {
        match mode {
            ContractMode::Always => Some(Ident::new("assert", span)),
            ContractMode::Debug => Some(Ident::new("debug_assert", span)),
            ContractMode::Test => Some(Ident::new("debug_assert", span)),
            ContractMode::Disabled => None,
            ContractMode::LogOnly => None,
        }
    }
}

/// Generate the resulting code for this function by inserting assertions.
pub(crate) fn generate(
    mut func: FuncWithContracts,
    docs: Vec<Attribute>,
    olds: Vec<OldExpr>,
) -> TokenStream {
    let func_name = func.function.sig.ident.to_string();

    // creates an assertion appropriate for the current mode
    let make_assertion = |mode: ContractMode,
                          ctype: ContractType,
                          display: proc_macro2::TokenStream,
                          exec_expr: &Expr,
                          desc: &str| {
        let span = display.span();
        let mut result = proc_macro2::TokenStream::new();
        let format_args = quote::quote_spanned! { span=>
            concat!(concat!(#desc, ": "), stringify!(#display))
        };

        if mode == ContractMode::LogOnly {
            result.extend(
                quote::quote_spanned! { span=>
                    if !(#exec_expr) {
                        log::error!(#format_args);
                    }
                }
                .into_iter(),
            );
        }

        if let Some(assert_macro) = get_assert_macro(ctype, mode, span) {
            result.extend(
                quote::quote_spanned! { span=>
                    #assert_macro!(#exec_expr, #format_args);
                }
                .into_iter(),
            );
        }

        if mode == ContractMode::Test {
            quote::quote_spanned! { span=>
              #[cfg(test)] {
                #result
              }
            }
        } else {
            result
        }
    };

    // creates an assertion with str instead of Expr, allow more design freedom
    let make_str_assertion = |mode: ContractMode,
                          ctype: ContractType,
                          display: proc_macro2::TokenStream,
                          exec_expr: &str,
                          desc: &str| {
        let span = display.span();
        let mut result = proc_macro2::TokenStream::new();

        let format_args = quote::quote_spanned! { span=>
            concat!(concat!(#desc, ": "), stringify!(#exec_expr))
        };

        if mode == ContractMode::LogOnly {
            result.extend(
                quote::quote_spanned! { span=>
                    if !(#exec_expr) {
                        log::error!(#format_args);
                    }
                }
                .into_iter(),
            );
        }

        if let Some(assert_macro) = get_assert_macro(ctype, mode, span) {
            result.extend(
                quote::quote_spanned! { span=>
                    #assert_macro!(#display, #format_args);
                }
                .into_iter(),
            );
        }

        if mode == ContractMode::Test {
            quote::quote_spanned! { span=>
            //   #[cfg(test)]
              {
                #result
              }
            }
        } else {
            result
        }
    };

    //
    // generate assertion code for pre-conditions
    //

    let pre: proc_macro2::TokenStream = func
        .contracts
        .iter()
        .filter(|c| {
            c.ty == ContractType::Requires || c.ty == ContractType::Invariant
        })
        .flat_map(|c| {
            let desc = if let Some(desc) = c.desc.as_ref() {
                format!(
                    "{} of {} violated: {}",
                    c.ty.message_name(),
                    func_name,
                    desc
                )
            } else {
                format!("{} of {} violated", c.ty.message_name(), func_name)
            };

            c.assertions.iter().zip(c.streams.iter()).map(
                move |(expr, display)| {
                    let mode = c.mode.final_mode();

                    make_assertion(
                        mode,
                        ContractType::Requires,
                        display.clone(),
                        expr,
                        &desc.clone(),
                    )
                },
            )
        })
        .collect();

    // a map for mr <index, mr info>,index is the mr number not the contract index
    let mut run_map:HashMap<usize, MRRunInfo> = HashMap::new();
    
    // whether use mr, for merge function body choice
    let mut used_contract_type = false;

    // function inputs and output type extraction
    let function_type = func.function.clone();
    let output_type = function_type.sig.output;

    // a map for variable type <variable name, variable type> for inputs and output, self not contain type info, so not included
    let mut variable_type: HashMap<String, String> = HashMap::new();
    variable_type.insert(String::from("ret"), output_type.clone().to_token_stream().to_string().split(" ").last().unwrap().to_string());
    
    // add input elements for variable type
    let function_signature = func.function.sig.clone();
    let _result: Vec<usize> = function_signature.inputs.iter().
    map(|arg|{
        match arg {
            FnArg::Typed(PatType { ty, pat, .. }) => {
                variable_type.insert(pat.to_token_stream().to_string(), ty.clone().to_token_stream().to_string().split(" ").last().unwrap().to_string());
                1
            },
            _ => 0,
        }
    }).collect();
    println!("variable_type {:?}", variable_type);
    // a vector for mutable variable for clone perparation
    let mut_para:Vec<_> = function_signature.inputs.iter().
    filter(|arg|{
        
        match arg {
            FnArg::Receiver(r) => r.mutability != None,
            FnArg::Typed(PatType { ty, .. })=> {
                match &**ty{
                    syn::Type::Reference(tr)=> {
                         tr.mutability != None
                    },
                    _ => false
                }
            }
        }
    }
        ).
    map(|arg|{
        match arg {
            FnArg::Receiver(r) => {
                match r.mutability {
                    Some(_) => "self".to_string(),
                    None=> String::new(),
                }
            }
            FnArg::Typed(PatType { ty, pat, .. }) => {
                match &**ty{
                    syn::Type::Reference(tr)=> {
                        match (tr.mutability,&**pat) {
                            (Some(_),_) => pat.to_token_stream().to_string(),
                            (None,_) => {
                                String::new()
                            },
                        }
                    },
                    _ => String::new()
                }
            }
        }}
    ).collect();
    println!("mut_para {:?}", mut_para);

    // FnArg::Typed(PatType { pat, .. }) => {
    //     match &**pat{
    //         Pat::Ident(i)=> {
    //             match i.mutability {
    //                 Some(_) => i.ident.to_string(),
    //                 None=> String::new()
    //             }
    //         },
    //         _ => String::new()
    //     }
    // }

    // clone and modify the variable used in the relationship
    let mut clone_variable = proc_macro2::TokenStream::new();
    let mut index = 0;
    let modify_para: proc_macro2::TokenStream = func
        .contracts
        .iter().enumerate()
        .filter(|pair| {
            let c = pair.1;
            c.ty == ContractType::Cyclicity || c.ty == ContractType::AddNotEqual || c.ty ==ContractType::LocalInvariance
            || c.ty == ContractType::Homomorphism || c.ty == ContractType::Monotonicity || c.ty == ContractType::IterConsistency
            || c.ty == ContractType::Symmetry
        })
        .flat_map(|pair| {
            let c = pair.1;
            let contract_index = pair.0;
            let para = c.streams.first().unwrap().clone();
            let para_string = para.to_string();
            // println!("{:?}", c.streams);
            let mut para_clone = para_string.clone();
            let mut _para_clone2 = para_string.clone();
            para_clone.push_str(format!("{}{}","_contract_", (index + 1).to_string()).as_str());
            let modi =c.streams[1].clone();
            let span = c.streams[0].span();
            let para = syn::Ident::new(&para_string, span);
            let para_clone = syn::Ident::new(&para_clone, span);
            let mut mut_def = quote::quote! {};
            if mut_para.contains(&para_string){
                mut_def = quote::quote! { mut };
            }
            
            let ret_type = variable_type.get(&String::from("ret")).unwrap();
            let mut para_type = variable_type.get(&para_string).unwrap();
            let sym_number = String::from("sym_number");
            let sym_func = String::from("sym_func");
            match (c.ty, c) {
                (ContractType::IterConsistency, _) => {
                    debug_assert!(ret_type == para_type, "wrong type, consistency can not satisfied");
                    let mut para_old = para_string.clone();
                    para_old.push_str("_contract_old");
                    let mr = MRRunInfo::new(contract_index, index + 1, 0, c.ty, para.clone(),para_string, modi.clone());
                    index += 1;
                    run_map.insert(contract_index, mr);
                    let para_old = syn::Ident::new(&para_old, span);
                    
                    let binding = quote::quote! {
                        let #para_old = #para.clone();
                    };            
                    binding
                }
                (ContractType::Homomorphism, _) => {
                    let op = c.streams[2].clone();
                    _para_clone2.push_str(format!("{}{}","_contract_", (index + 2).to_string()).as_str());
                    let para_clone2 = syn::Ident::new(&_para_clone2, span);
                    let mr = MRRunInfo::new(contract_index, index + 1, index + 2, c.ty, para.clone(),para_string, modi.clone());
                    run_map.insert(contract_index, mr);
                    index += 2;
                    let mut first_modi = modi.clone();
                    if para_type == "String"{
                        first_modi = quote::quote! {#modi.to_string();}
                    }
                    let first_assign = quote::quote! {
                        let #mut_def #para_clone = #first_modi;
                    };
                    let second_assign = merge_statement(para_type.as_str(), &para, &modi, &op, &mut_def, &para_clone2);
                    let binding = quote::quote! {
                        #first_assign
                        #second_assign
                    };
                    binding
                }
                (_,_) => {
                    let mut op = c.streams[2].clone();
                    if c.ty == ContractType::Symmetry{
                        if ["f32", "f64", "i128" , "i16" , "i32" , "i64" , "i8", "isize" , "u128" , "u16" , "u32" , "u64" , "u8" , "usize"].contains(&para_type.as_str()){
                            para_type = &sym_number;
                        }
                        else if ["String", "str"].contains(&para_type.as_str()){
                            panic!("undefined symmetry for string");
                        }
                        else{
                            para_type = &sym_func;
                        }
                    }
                    if c.ty == ContractType::Monotonicity{
                        if ["f32", "f64", "i128" , "i16" , "i32" , "i64" , "i8", "isize" , "u128" , "u16" , "u32" , "u64" , "u8" , "usize", "str", "String"].contains(&para_type.as_str()){
                            
                            let op_syn:proc_macro2::Punct = syn::parse_str("+").unwrap();
                            op = op_syn.to_token_stream();
                        }
                    }
                    let mr = MRRunInfo::new(contract_index, index + 1, 0, c.ty, para.clone(),para_string, modi.clone());
                    index += 1;
                    run_map.insert(contract_index, mr);
                    let binding = merge_statement(para_type.as_str(), &para, &modi, &op, &mut_def, &para_clone);
                    // let binding = quote::quote! {
                    //     let #para_clone = format!("{}{}", #para , #modi);
                    //     let #mut_def #para_clone = #para_clone.as_str();
                    // };     
                    binding
                }
            }
            
        }).collect();
        clone_variable.extend(modify_para);
        println!("clone_variable:{}", clone_variable);

    //  generate corresponding assertions based on mr
    let mr: proc_macro2::TokenStream = func
        .contracts
        .iter().enumerate()
        .filter(|pair| {
            let c = pair.1;
            c.ty == ContractType::Cyclicity || c.ty == ContractType::AddNotEqual || c.ty ==ContractType::LocalInvariance
            || c.ty == ContractType::Homomorphism || c.ty == ContractType::Monotonicity || c.ty == ContractType::IterConsistency
            || c.ty == ContractType::Symmetry
        })
        .flat_map(|pair| {
            // println!("{:?}", c);
            let c = pair.1;
            let contract_index = pair.0;
            let mr_info_reuslt = run_map.get(&contract_index);
            let mr_info = match mr_info_reuslt{
                Some(info) => info,
                None => panic!("i have not handled the contract right, check the index.")
            };
            let second_run_index = mr_info.retindex1;
            used_contract_type = true;
            let desc = if let Some(desc) = c.desc.as_ref() {
                format!(
                    "{} of {} violated: {}",
                    c.ty.message_name(),
                    func_name,
                    desc
                )
            } else {
                format!("{} of {} violated", c.ty.message_name(), func_name)
            };
            

            let mode = c.mode.final_mode();

            let ret_type = variable_type.get(&String::from("ret")).unwrap();
            let mut op = TokenStream::new();
            if c.streams.len() > 2{
                op = c.streams[2].clone();
                match ret_type.as_str(){
                    "f32"| "f64"| "i128"| "i16"| "i32"| "i64"| "i8"| "isize"| "u128"| "u16"| "u32"| "u64"| "u8"| "usize" =>{
                        if op.to_string().chars().nth(0).unwrap().is_ascii_alphabetic(){
                            op = proc_macro2::Punct::new(char::from(43), proc_macro2::Spacing::Alone).to_token_stream();
                        }
                    },
                    _ => (),
                }
            }
            let span = Span::call_site();
            let ret1 = syn::Ident::new(format!("{}{}", "ret", second_run_index).as_str(), span);
            let ret_str_ident = syn::Ident::new("ret", span);

            let ret = match (c.ty, c) {
                (ContractType::Cyclicity, _) => {
                    make_str_assertion(
                        mode,
                        ContractType::Cyclicity,
                        quote::quote! {ret == #ret1},
                        "f(x + t) = f(x)",
                        &desc.clone(),
                    )
                }
                (ContractType::AddNotEqual, _) => {
                    make_str_assertion(
                        mode,
                        ContractType::AddNotEqual,
                        quote::quote! {ret != #ret1},
                        "f(x + y) != f(x)",
                        &desc.clone(),
                    )
                }
                (ContractType::LocalInvariance, c) => {
                    let x = c.streams[1].clone();
                    // let op = c.streams[2].clone();
                    let a = merge_expr(ret_type, &ret_str_ident, &syn::Ident::new(x.to_string().as_str(), span), &op);
                    let asserts = quote::quote! {#a == #ret1};
                    // let asserts = quote::quote! {ret + #x == #ret1};
                    make_str_assertion(
                        mode,
                        ContractType::LocalInvariance,
                        asserts,
                        "f(x + y) = f(x)",
                        &desc.clone(),
                    )
                }
                (ContractType::Symmetry, _) => {
                    let mut sign = TokenStream::new();
                    if ["f32", "f64", "i128" , "i16" , "i32" , "i64" , "i8", "isize" , "u128" , "u16" , "u32" , "u64" , "u8" , "usize", "str", "String"].contains(&ret_type.as_str()){
                        sign = proc_macro2::Punct::new(c.streams[2].clone().to_string().as_str().chars().nth(0).unwrap(), proc_macro2::Spacing::Alone).to_token_stream();
                    }
                    let asserts = quote::quote! {ret == #sign #ret1};
                    make_str_assertion(
                        mode,
                        ContractType::Symmetry,
                        asserts,
                        "f(x) = ±f(2*y - x)",
                        &desc.clone(),
                    )
                }
                (ContractType::Homomorphism, _) => {
                    let third_run_index = mr_info.retindex2;
                    // let op = c.streams[2].clone();
                    let ret2 = syn::Ident::new(format!("{}{}", "ret", third_run_index).as_str(), span);
                    let a = merge_expr(ret_type, &ret1, &ret2, &op);
                    let asserts = quote::quote! {ret == #a};
                    // let asserts = quote::quote! {ret == #ret1 + #ret2};
                    make_str_assertion(
                        mode,
                        ContractType::Homomorphism,
                        asserts,
                        "f(x) + f(y) = f(x + y)",
                        &desc.clone(),
                    )
                }
                (ContractType::IterConsistency, _) => {
                    let para = syn::Ident::new(format!("{}{}", mr_info.variable_name, "_contract_old").as_str(), span);
                    op = c.streams[1].clone();
                    // let op = c.streams[2].clone();
                    let a = merge_expr(ret_type, &ret_str_ident, &ret_str_ident, &op);
                    let b = merge_expr(ret_type, &ret1, &para, &op);
                    let asserts = quote::quote! {#a == #b};
                    // let asserts = quote::quote! {ret + ret == #ret1 + #para};
                    make_str_assertion(
                        mode,
                        ContractType::IterConsistency,
                        asserts,
                        "f(f(x)) - f(x) = f(x) - x",
                        &desc.clone(),
                    )
                }
                (ContractType::Monotonicity, _) => {
                    // let op = c.streams[2].clone();
                    // let a = merge_expr(ret_type, &ret_str_ident, &ret1, &op);
                    // let asserts = quote::quote! {#a};
                    let asserts;
                    if op.to_string().chars().nth(0).unwrap().is_ascii_alphabetic(){
                        asserts = quote::quote! {ret.#op(#ret1)};
                    }else{
                        asserts = quote::quote! {ret #op #ret1};
                    }
                    make_str_assertion(
                        mode,
                        ContractType::Monotonicity,
                        asserts,
                        "x < y -> f(x) < f(y)",
                        &desc.clone(),
                    )
                }
                (_,_) => {
                    println!("not a mr relation");
                    TokenStream::new()
                }
            };
            
            ret
        })
        .collect();
        // println!("{}", mr);


    let mut_para1 = mut_para.clone();

    let mut clone_mut = proc_macro2::TokenStream::new();
    println!("{:?}", run_map);
    println!("{:?}", index);
    for run_ind in 0..func.contracts.len(){
        let mr_info_result = run_map.get(&run_ind);
        let mr_info = match mr_info_result {
            Some(info) => info,
            None => continue,
        };
        let run_index = mr_info.retindex1.clone();
        let para_string = mr_info.variable_name.clone();
        for para in &mut_para{
            if para_string == *para{
                continue;
            }
            let mut para_clone = para.clone();
            para_clone.push_str(format!("{}{}","_contract_", run_index.to_string()).as_str());
            let span = clone_mut.span();
            let para = syn::Ident::new(&para, span);
            let para_clone = syn::Ident::new(&para_clone, span);
            let binding = quote::quote! {
                let mut #para_clone = #para .clone();
            };
            clone_mut.extend(Some(binding));
        }
        let run_index2 = mr_info.retindex2.clone();
        if run_index2 != 0{
            for para in &mut_para{
                if para_string == *para{
                    continue;
                }
                let mut para_clone = para.clone();
                para_clone.push_str(format!("{}{}","_contract_", run_index2.to_string()).as_str());
                let span = clone_mut.span();
                let para = syn::Ident::new(&para, span);
                let para_clone = syn::Ident::new(&para_clone, span);
                let binding = quote::quote! {
                    let mut #para_clone = #para .clone();
                };
                clone_mut.extend(Some(binding));
            }
        }
    }
    println!("clone def: {}", clone_mut);
        
    //
    // generate assertion code for post-conditions
    //

    let post: proc_macro2::TokenStream = func
        .contracts
        .iter()
        .filter(|c| {
            c.ty == ContractType::Ensures || c.ty == ContractType::Invariant
        })
        .flat_map(|c| {
            let desc = if let Some(desc) = c.desc.as_ref() {
                format!(
                    "{} of {} violated: {}",
                    c.ty.message_name(),
                    func_name,
                    desc
                )
            } else {
                format!("{} of {} violated", c.ty.message_name(), func_name)
            };

            c.assertions.iter().zip(c.streams.iter()).map(
                move |(expr, display)| {
                    let mode = c.mode.final_mode();

                    make_assertion(
                        mode,
                        ContractType::Ensures,
                        display.clone(),
                        expr,
                        &desc.clone(),
                    )
                },
            )
        })
        .collect();

    //
    // bind "old()" expressions
    //

    let olds = {
        let mut toks = proc_macro2::TokenStream::new();

        for old in olds {
            let span = old.expr.span();

            let name = syn::Ident::new(&old.name, span);

            let expr = old.expr;

            let binding = quote::quote_spanned! { span=>
                let #name = #expr;
            };

            toks.extend(Some(binding));
        }

        toks
    };

    //
    // wrap the function body in a closure
    //

    let block = func.function.block.clone();

    let ret_ty = match &func.function.sig.output {
        ReturnType::Type(_, ty) => {
            let span = ty.span();
            match ty.as_ref() {
                syn::Type::ImplTrait(_) => quote::quote! {},
                ty => quote::quote_spanned! { span=>
                    -> #ty
                },
            }
        }
        ReturnType::Default => quote::quote! {},
    };

    let body = quote::quote! {
        #[allow(unused_mut)]
        let mut run = || #ret_ty #block;

        let ret = run();
    };

    let perpare_and_body = quote::quote! {
            #pre

            #body
    };
    println!("original body: {}", perpare_and_body);

    //
    // create a new function body containing all assertions
    //

    let mut extra_body:TokenStream = proc_macro2::TokenStream::new();
    for i in 0..func.contracts.len(){    
        // println!("{:?}", run_map);
        // println!("{:?}", i);
        let mr_info_result = run_map.get(&i);
        let mr_info = match mr_info_result {
            Some(info) => info,
            None => continue,
        };
        let second_run_index = mr_info.retindex1;
        println!("generating mr: {:?}", mr_info.mr);
        let clone_last:TokenStream = match mr_info.mr {
            ContractType::IterConsistency => {
                let span = Span::call_site();
                let para1 = syn::Ident::new(format!("{}{}{}", mr_info.variable.to_string(), "_contract_", second_run_index).as_str(), span);
                quote::quote! {
                    let #para1 = ret.clone();
                }
            },
            _ => quote::quote! {},
        };
        // println!("clone last: {:?}", clone_last);

        
        let key = &mr_info.variable.to_string();
        println!("{}", key);
            
        let mut one_extra_run = |second_run_index| {
            let preforclone: proc_macro2::TokenStream = func
            .contracts
            .iter().enumerate()
            .filter(|pair| {
                let c = pair.1;
                c.ty == ContractType::Requires
            })
            .flat_map(|pair| {
                // println!("{:?}", c);
                let c = pair.1;
                let desc = if let Some(desc) = c.desc.as_ref() {
                    format!(
                        "{} of {} violated for extra run: {}",
                        c.ty.message_name(),
                        func_name,
                        desc
                    )
                } else {
                    format!("{} of {} violated", c.ty.message_name(), func_name)
                };

                let keyclone = key.clone();
                c.assertions.iter().zip(c.streams.iter()).map(
                    move |(expr, display)| {
                        let mode = c.mode.final_mode();
                        
                        let expr = expr.into_token_stream().to_string().replace(
                            format!("{}", keyclone).as_str(), format!(" {}{}{} ", keyclone, "_contract_", second_run_index).as_str());
                        // expr = expr.replace("\n", "");
                        let expr_result = syn::parse_str::<Expr>(expr.as_str());
                        let expr = match expr_result{
                            Ok(expr) => expr,
                            Err(e) => {
                                println!("{}", expr);
                                println!("{}", e);
                                panic!("wrong construction of pre-condition for extra run body.");
                            },
                        };
                        make_assertion(
                            mode,
                            ContractType::Requires,
                            display.clone(),
                            &expr,
                            &desc.clone(),
                        )
                    },
                )
            })
            .collect();
        // println!("pre for clone: {:?}", preforclone);

        let block_attrs = func.function
                .block.clone();

        let mut block_attrs = block_attrs.to_token_stream().to_string();
        for para in &mut_para1{
            block_attrs = block_attrs.replace(format!(" {} ", para).as_str(), format!(" {}{}{} ", para, "_contract_", second_run_index).as_str());
        }

        block_attrs = block_attrs.replace(format!("{}", key).as_str(), format!("{}{}{} ", key, "_contract_", second_run_index).as_str());
        block_attrs = block_attrs.replace("\n", "");
        // println!("{:?}", block_attrs);
        let block_attrs = syn::parse_str::<Expr>(block_attrs.as_str()).unwrap();
        // println!("{:?}", &block_attrs);

        let second_run_body = new_function_body_with_index(second_run_index, ret_ty.clone(), block_attrs);
        // println!("{}", second_run_body);

        let new_body:TokenStream = quote::quote! {

                #clone_last

                #preforclone

                #second_run_body
        };
        // println!("{:?}", new_body);
        extra_body.extend(new_body);
        };
        match mr_info.mr {
            ContractType::Homomorphism => {
                one_extra_run(second_run_index);
                one_extra_run(second_run_index + 1);
            },
            _ => one_extra_run(second_run_index),
        };
    }


    let _old_block = quote::quote! {

        {
            #pre

            #olds

            #body

            #post

            ret
        }

    };

    // let print = quote::quote! {

    //     println!("{}", ret == ret1 + ret2);
    // };

    let new_block:TokenStream = quote::quote! {

        {
            #olds

            #clone_variable

            #clone_mut

            #perpare_and_body

            #extra_body

            #mr

            #post

            // #print

            ret
        }
    };
    
    println!("{}", new_block);

    // insert documentation attributes

    func.function.attrs.extend(docs);

    // replace the old function body with the new one

    func.function.block = Box::new(syn::parse_quote!(#new_block));

    func.function.into_token_stream()
}

fn new_function_body_with_index(index: usize, ret_ty: TokenStream, block_attrs: Expr) -> TokenStream{
    let span = Span::call_site();
    let run1 = syn::Ident::new(format!("{}{}", "run", index).as_str(), span);
    let ret1 = syn::Ident::new(format!("{}{}", "ret", index).as_str(), span);
    let run_body:TokenStream = quote::quote! {
        #[allow(unused_mut)]
        let mut #run1 = || #ret_ty #block_attrs;

        let #ret1 = #run1();
    };
    run_body
}

fn merge_statement(type_str: &str , para: &syn::Ident, modi: &TokenStream, 
    op: &TokenStream, mut_def: &TokenStream, para_clone: &syn::Ident) -> TokenStream {
    let op_syn:proc_macro2::TokenTree = syn::parse2(op.clone()).unwrap();
    match (type_str,op_syn){
        ("str", proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            // (#para.to_string().push_str(#modi)).as_str()
            let #mut_def #para_clone = format!("{}{}", #para.to_string(),#modi.to_string());
            let #mut_def #para_clone = #para_clone.as_str();
        },
        ("String",_) => {
            quote::quote! {
                let #mut_def #para_clone = #para.clone()#op#modi;
            }
        },
        ("f32",_) | ("f64",_)| ("i128",_) | ("i16" ,_)| ("i32",_) | ("i64",_) | ("i8",_)| ("isize" ,_)| ("u128",_) | ("u16",_) | ("u32",_) | ("u64",_) | ("u8",_) | ("usize",_) => quote::quote! {
            let #mut_def #para_clone = #para#op#modi;
        },
        ("sym_number",_) => quote::quote! {
            let #mut_def #para_clone = 2 * #modi #op #para;
        },
        ("sym_func",_) => quote::quote! {
            let #mut_def #para_clone = #para.clone();
            let #mut_def #para_clone = #para_clone.#modi();
        },
        (_ ,_)=>quote::quote! {
            let #mut_def #para_clone = #para.clone();
            let #mut_def #para_clone = #para_clone.#op(#modi);
        },
    }
}

fn merge_expr(type_str: &str , para: &syn::Ident, modi: &syn::Ident, op: &TokenStream) -> TokenStream {
    let op_syn:proc_macro2::TokenTree = syn::parse2(op.clone()).unwrap();
    match (type_str,op_syn){
        ("str", proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            format!("{}{}", #para.to_string(),#modi.to_string()).as_str()
        },
        ("String",_) => {
            quote::quote! {
                format!("{}{}", #para,#modi).as_str()
            }
        },
        ("f32",_) | ("f64",_)| ("i128",_) | ("i16" ,_)| ("i32",_) | ("i64",_) | ("i8",_)| ("isize" ,_)| ("u128",_) | ("u16",_) | ("u32",_) | ("u64",_) | ("u8",_) | ("usize",_) => quote::quote! {
            #para#op#modi
        },
        (_ ,_)=>quote::quote! {
             #para.clone().#op(#modi.clone())
        },
    }
}
