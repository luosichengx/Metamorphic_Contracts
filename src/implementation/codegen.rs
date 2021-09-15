/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use proc_macro2::{Ident, Span, TokenStream};
use quote::ToTokens;
use syn::{Attribute, Expr, ExprCall, FnArg, PatType, ReturnType, spanned::Spanned, visit_mut::{self as visitor, VisitMut}};

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

pub struct MRInfo{
    /// index of the variable binder.
    pub index: usize,
    /// mr relation
    mr:ContractType,
    pub runinfos: Vec<RunInfo>,
}

pub struct RunInfo{
    pub retindex: usize,
    pub variables: Vec<Ident>,
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

impl RunInfo{
    fn new(retindex: usize, variables: Vec<Ident>)->Self{
        RunInfo{
            retindex,
            variables,
        }
    }
}

impl MRInfo{
    fn new(index: usize, mr:ContractType, runinfos: Vec<RunInfo>)->Self{
        MRInfo{
            index,
            mr,
            runinfos,
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
            // use visitor::VisitMut;
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
            (ContractType::Periodicity, _) => {
                Some(Ident::new("periodicity", span))
            }
            (ContractType::AddNotEqual, _) => {
                Some(Ident::new("check_add_not_equal", span))
            }
            (ContractType::DimensionTrans, _) => {
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
            (ContractType::Mapping, _) => {
                Some(Ident::new("mapping", span))
            }
            (ContractType::MR, _) => {
                Some(Ident::new("mr", span))
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

struct ParaModifiction<'a>{
    function_name: String,
    input_len: usize,
    index: usize,
    // c: Contract,
    // all para list
    inputs: &'a Vec<String>,
    // the thing we need
    para_binding: TokenStream,
    //return modi para
    variables: Vec<String>,
}


struct ParafindReplace<'a, 'b>{
    variables: &'a Vec<String>,
    base_variable: String,
    para_binding: TokenStream,
    ret_index: usize,
    clone_index: &'b mut usize,
}

impl<'a, 'b> VisitMut for ParafindReplace<'a, 'b> {
    fn visit_ident_mut(&mut self, i: &mut Ident) {
        let ident_string = i.to_string();
        if self.base_variable.is_empty(){
            self.base_variable = ident_string.clone();
        }
        if self.variables.contains(&ident_string){
            let paraclone = format!("{}{}{}{}",ident_string, self.clone_index, "_contract_", self.ret_index);
            let paracloneident = syn::Ident::new(paraclone.as_str(), Span::call_site());
            *self.clone_index = *self.clone_index + 1;
            self.para_binding.extend(quote::quote! {
                let #paracloneident = #i.clone();
            });
            *i = syn::Ident::new(paraclone.as_str(), i.span());
        }
    }
}

impl<'a> ParaModifiction<'a> {
    pub fn change_for_variable(&self, var:&str, new_para:&mut Expr, clone_index:&mut usize, not_change:&mut bool) -> TokenStream{
        let mut binding = TokenStream::new();
        let mut changed_variables = Vec::new();
        let new_para_string = new_para.to_token_stream().to_string();
        if new_para_string == *var{
            return binding
        }
        let mut parafindreplace = ParafindReplace{variables: self.inputs, base_variable: var.to_string(), para_binding: TokenStream::new(), ret_index: self.index, clone_index: clone_index};
        parafindreplace.visit_expr_mut(new_para);
        if parafindreplace.base_variable.is_empty(){
            panic!("not enough parameter for all inputs and the given input does not have base para")
        }
        if changed_variables.contains(&parafindreplace.base_variable){
            panic!("not enough parameter for all inputs, but the given inputs have duplicate para")
        }
        changed_variables.push(parafindreplace.base_variable.clone());
        binding.extend(parafindreplace.para_binding);
        let var_clone;
        if var == ""{
            var_clone = syn::Ident::new(parafindreplace.base_variable.as_str(), Span::call_site());
        }else{
            var_clone = syn::Ident::new(&var, Span::call_site());
        }
        if new_para_string == parafindreplace.base_variable{
            return binding
        }
        let a = new_para.to_token_stream();
        let var_clone_ident = syn::Ident::new(format!("{}{}{}",var_clone, "_contract_", self.index).as_str(), Span::call_site());
        binding.extend(quote::quote! {
            let mut #var_clone_ident = #a;
        });
        *not_change = false;
        binding
    }
}


impl<'a> VisitMut for ParaModifiction<'a> {
    fn visit_expr_call_mut(&mut self, i: &mut ExprCall) {
        println!("{}", i.to_token_stream().to_string());
        let mut clone_index:usize = 0;
        let mut not_change = true;
        let mut binding = TokenStream::new();
        if i.func.to_token_stream().to_string() == self.function_name{
            if self.input_len != i.args.len(){
                for x in &mut i.args{
                    // println!("{} {:?}", "notsure", x);
                    binding.extend(ParaModifiction::<'a>::change_for_variable(self, "",  x, &mut clone_index, &mut not_change));
                }
            }else{
                for x in 0..i.args.len(){
                    // println!("{} {:?}",self.inputs[x], i.args[x]);
                    binding.extend(ParaModifiction::<'a>::change_for_variable(self, &self.inputs[x], &mut i.args[x], &mut clone_index, &mut not_change));
                }
            };
            self.index += 1;
            if not_change == true{
                binding = TokenStream::new();
            }
            self.para_binding.extend(binding);
        }else{
            visitor::visit_expr_call_mut(self, i);
        }
    }

    
    fn visit_expr_method_call_mut(&mut self, i: &mut syn::ExprMethodCall) {
        let mut clone_index:usize = 0;
        let mut not_change = true;
        let mut binding = TokenStream::new();
        if i.method.to_token_stream().to_string() == self.function_name{
            if self.input_len != i.args.len() + 1{
                for x in &mut i.args{
                    binding.extend(ParaModifiction::<'a>::change_for_variable(self, "a",  x, &mut clone_index, &mut not_change));
                }
            }else{
                for x in 0..i.args.len(){
                    binding.extend(ParaModifiction::<'a>::change_for_variable(self, &self.variables[x], &mut i.args[x], &mut clone_index, &mut not_change));
                }
            };
            self.index += 1;   
            if not_change == true{
                self.para_binding = TokenStream::new();
            }
            self.para_binding.extend(binding);
        }else{
            visitor::visit_expr_method_call_mut(self, i);
        }
    }
}


struct ParaReplace{
    old_para: String,
    new_para: String,
}

impl VisitMut for ParaReplace {
    fn visit_ident_mut(&mut self, i: &mut Ident) {
        let ident_string = i.to_token_stream().to_string();
        if ident_string == self.old_para{
            // println!("{} {}",ident_string, self.old_para);
            *i = syn::Ident::new(self.new_para.as_str(), i.span());
        }
    }

    fn visit_expr_mut(&mut self, node: &mut Expr) {
        // println!("test ident {:?}", node);
        // println!("test ident {}", node.to_token_stream().to_string());
        // println!("compare with {:?}", self.old_para);
        if let Expr::Unary(exprunary) = &node {
            if exprunary.op.to_token_stream().to_string() == String::from("*") && exprunary.expr.to_token_stream().to_string() == self.old_para{
                *node = *exprunary.expr.clone();
            }
        }
        if let Expr::Path(expr) = &node {
            let ident_result = expr.path.get_ident();
            match ident_result{
                Some(ident)=> {
                    let ident_string = ident.to_string();
                    if ident_string == self.old_para{
                        // println!("{}", ident_string);
                        *node = syn::parse_str(self.new_para.as_str()).unwrap();
                    }
                },
                None => (),
            }
            return
        }
        
        // Delegate to the default impl to visit nested expressions.
        visitor::visit_expr_mut(self, node);
        
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
    let mut function_inputs = Vec::new();
    let ret_type_string= output_type.clone().to_token_stream().to_string();
    if ret_type_string.contains("Result"){
        variable_type.insert(String::from("ret"), String::from("Result"));
    }
    else if ret_type_string.contains("Option"){
        variable_type.insert(String::from("ret"), String::from("Option"));
    }
    else{
        variable_type.insert(String::from("ret"), output_type.clone().to_token_stream().to_string().split(" ").last().unwrap().to_string());
    }

    // add input elements for variable type
    let function_signature = func.function.sig.clone();
    function_signature.inputs.iter().
    for_each(|arg|{
        match arg {
            FnArg::Receiver(r) => {
                function_inputs.push(String::from("self"));
            },
            FnArg::Typed(PatType { ty, pat, .. }) => {
                variable_type.insert(pat.to_token_stream().to_string().split(" ").last().expect("no variable name here").to_string(), ty.clone().to_token_stream().to_string().split(" ").last().expect("input para type parse error").to_string());
                function_inputs.push(pat.to_token_stream().to_string().split(" ").last().expect("no variable name here").to_string())
            },
            _ => {},
        }
    });
    println!("variable_type {:?}", variable_type);

    let input_len = func.function.sig.inputs.len();
    let the_function_name = func.function.sig.ident.to_string();

    // a vector for mutable variable for clone perparation
    let mut_para:Vec<_> = function_signature.inputs.iter().
    filter_map(|arg|{
        match arg {
            FnArg::Receiver(r) => {
                match r.mutability {
                    Some(_) => Some("self".to_string()),
                    None=> None,
                }
            },
            FnArg::Typed(PatType { ty, pat, .. })=> {
                match (&**ty, &**pat){
                    (syn::Type::Reference(tr), syn::Pat::Ident(i)) => {
                        match tr.mutability{
                            Some(_) => Some(i.ident.to_string()),
                            None => None,
                        }
                    },
                    (_, syn::Pat::Ident(i))=>{
                        match i.mutability{
                            Some(_) => Some(i.ident.to_string()),
                            None => None,
                        }
                    },
                    _ => None,
                }
            }
        }
    }).collect();
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
    let self_type = String::from("struct");

    // clone and modify the variable used in the relationship
    let mut clone_variable = proc_macro2::TokenStream::new();
    let mut index = 0;

    let mut return_here = false;
    let modify_para: proc_macro2::TokenStream = func
        .contracts
        .iter().enumerate()
        .filter(|pair| {
            let c = pair.1;
            c.ty == ContractType::Periodicity || c.ty == ContractType::AddNotEqual || c.ty ==ContractType::DimensionTrans
            || c.ty == ContractType::Homomorphism || c.ty == ContractType::Monotonicity || c.ty == ContractType::IterConsistency
            || c.ty == ContractType::Symmetry || c.ty == ContractType::Mapping ||c.ty == ContractType::MR
        })
        .flat_map(|pair| {
            let c = pair.1;
            // println!("{:?}", c.streams);
            let contract_index = pair.0;
            let para_number = c.streams.len();
            if c.ty == ContractType::MR{
                let mut a = c.assertions[0].clone();
                let mut paramodi = ParaModifiction{function_name: the_function_name.clone(), input_len, index, inputs: &function_inputs, para_binding: TokenStream::new(), variables: Vec::new() };
                paramodi.visit_expr_mut(&mut a);
                return_here = true;
                return paramodi.para_binding
            }
            let para = c.streams.first().expect("No para here").clone();
            let para_string = para.to_string();
            let mut para_clone = para_string.clone();
            let mut _para_clone2 = para_string.clone();
            para_clone.push_str(format!("{}{}","_contract_", (index + 1).to_string()).as_str());
            let modi:TokenStream;
            if para_number > 2{
                modi = c.streams[2].clone();
            }else{
                modi = TokenStream::new();
            }
            let span = c.streams[0].span();
            let para = syn::Ident::new(&para_string, span);
            let para_clone = syn::Ident::new(&para_clone, span);
            let mut mut_def = quote::quote! {};
            if mut_para.contains(&para_string){
                mut_def = quote::quote! { mut };
            }
            
            let ret_type = variable_type.get(&String::from("ret")).expect("No ret type in variable type");
            let mut para_type;
            if para_string == String::from("self"){
                para_type = &self_type;
            }
            else{
                para_type = variable_type.get(&para_string).expect("No para type in variable type");
            }
            let sym_number = String::from("sym_number");
            let sym_float = String::from("sym_float");
            let sym_func = String::from("sym_func");
            let sym_bool = String::from("sym_bool");
            match (c.ty, c) {
                (ContractType::IterConsistency, _) => {
                    if *para_type != self_type{
                        debug_assert!(ret_type == para_type, "wrong type, consistency can not satisfied");
                    }
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
                    let op = c.streams[1].clone();
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
                (ContractType::Mapping, _) => {
                    let op = c.streams[1].clone();
                    _para_clone2.push_str(format!("{}{}","_contract_", (index + 2).to_string()).as_str());
                    let para_clone2 = syn::Ident::new(&_para_clone2, span);
                    let mr = MRRunInfo::new(contract_index, index + 1, index + 2, c.ty, para.clone(),para_string, modi.clone());
                    // println!("{:?}", mr);
                    run_map.insert(contract_index, mr);
                    index += 2;
                    let first_assign = merge_statement(para_type.as_str(), &para, &modi, &op, &mut_def, &para_clone);
                    let second_assign = merge_statement(para_type.as_str(), &para_clone, &modi, &op, &mut_def, &para_clone2);
                    let binding = quote::quote! {
                        #first_assign
                        #second_assign
                    };
                    binding
                }
                (_,_) => {
                    let op = c.streams[1].clone();
                    println!("{}",para_type);
                    if c.ty == ContractType::Symmetry{
                        if ["i128" , "i16" , "i32" , "i64" , "i8", "isize" , "u128" , "u16" , "u32" , "u64" , "u8" , "usize"].contains(&para_type.as_str()){
                            para_type = &sym_number;
                        }
                        else if ["f32", "f64", "float"].contains(&para_type.as_str()){
                            para_type = &sym_float;
                        }
                        else if "bool" == para_type.as_str(){
                            para_type = &sym_bool;
                        }
                        else if ["String", "str"].contains(&para_type.as_str()){
                            panic!("undefined symmetry for string");
                        }
                        else{
                            para_type = &sym_func;
                        }
                    }
                    let mr = MRRunInfo::new(contract_index, index + 1, 0, c.ty, para.clone(),para_string, modi.clone());
                    index += 1;
                    run_map.insert(contract_index, mr);
                    let mut binding = TokenStream::new();
                    if c.ty == ContractType::DimensionTrans{
                        
                        let modi_old = syn::Ident::new("_modi_contract_old", span);
                        binding.extend(quote::quote! {
                            let #modi_old = #modi.clone();
                        });
                    }
                    binding.extend(merge_statement(para_type.as_str(), &para, &modi, &op, &mut_def, &para_clone));
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

    if return_here == true{
        return TokenStream::new();
    }

    let mut result_unwrapped = false;
    //  generate corresponding assertions based on mr
    let mr: proc_macro2::TokenStream = func
        .contracts
        .iter().enumerate()
        .filter(|pair| {
            let c = pair.1;
            c.ty == ContractType::Periodicity || c.ty == ContractType::AddNotEqual || c.ty ==ContractType::DimensionTrans
            || c.ty == ContractType::Homomorphism || c.ty == ContractType::Monotonicity || c.ty == ContractType::IterConsistency
            || c.ty == ContractType::Symmetry || c.ty == ContractType::Mapping
        })
        .flat_map(|pair| {
            let c = pair.1;
            // println!("{:?}", c);
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
            let mut op = c.streams[1].clone();
            let mut extra_op = TokenStream::new();
            if c.streams.len() > 3{
                extra_op = c.streams[3].clone();
                match ret_type.as_str(){
                    "f32"| "f64"| "i128"| "i16"| "i32"| "i64"| "i8"| "isize"| "u128"| "u16"| "u32"| "u64"| "u8"| "usize" =>{
                        if op.to_string().chars().nth(0).expect("operator not implement correctly").is_ascii_alphabetic(){
                            op = proc_macro2::Punct::new(char::from(43), proc_macro2::Spacing::Alone).to_token_stream();
                        }
                    },
                    _ => (),
                }
            }
            let mut extra_modi = TokenStream::new();
            if c.streams.len() > 4{
                extra_modi = c.streams[4].clone();
            }
            let span = Span::call_site();
            let ret1 = syn::Ident::new(format!("{}{}", "ret", second_run_index).as_str(), span);
            let ret_str_ident = syn::Ident::new("ret", span);
            let mut ret0_unwrap:TokenStream = TokenStream::new();

            let ret = match (c.ty, c) {
                (ContractType::Periodicity, _) => {
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::Periodicity,
                        quote::quote! {#ret1 == ret},
                        "f(x + t) = f(x)",
                        &desc.clone(),
                    );
                    result_unwrapped = true;
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #assert_stream
                    }
                }
                (ContractType::AddNotEqual, _) => {
                    make_str_assertion(
                        mode,
                        ContractType::AddNotEqual,
                        quote::quote! {#ret1 != ret},
                        "f(x + y) != f(x)",
                        &desc.clone(),
                    )
                }
                (ContractType::DimensionTrans, _) => {
                    // let op = c.streams[1].clone();
                    if extra_op.is_empty(){
                        println!("Dimension transformation require three arguments, op, modi, second_op");
                        return extra_op;
                    };
                    let modi_contract_old = syn::Ident::new("_modi_contract_old", span);
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    let a:TokenStream;
                    if ! extra_modi.is_empty(){
                        let extra_modi_ident:TokenStream = syn::parse2(extra_modi).expect("extra modi can't parse");
                        a = merge_expr(ret_type, &ret_str_ident, &extra_modi_ident, &extra_op);
                    }
                    else{
                        a = merge_expr(ret_type, &ret_str_ident, &modi_contract_old.to_token_stream(), &extra_op);
                    }
                    let asserts = quote::quote! {#ret1 == #a};
                    // let asserts = quote::quote! {ret + #x == #ret1};
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::DimensionTrans,
                        asserts,
                        "f(x + y) = f(x) + y",
                        &desc.clone(),
                    );
                    result_unwrapped = true;
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #assert_stream
                    }
                }
                (ContractType::Symmetry, _) => {
                    // let mut sign = TokenStream::new();
                    if extra_op.is_empty(){
                        println!("Dimension transformation require three arguments, op, modi, second_op");
                        return extra_op;
                    };
                    let sign = match extra_op.clone().to_string().as_str(){
                        "+" => TokenStream::new(),
                        "-" => proc_macro2::Punct::new('-', proc_macro2::Spacing::Alone).to_token_stream(),
                        _ => {println!("sign operator should be in + or -");
                            TokenStream::new()
                        },
                    };
                    // if ["f32", "f64", "i128" , "i16" , "i32" , "i64" , "i8", "isize" , "u128" , "u16" , "u32" , "u64" , "u8" , "usize", "str", "String"].contains(&ret_type.as_str()){
                    // sign = proc_macro2::Punct::new(c.streams[3].clone().to_string().as_str().chars().nth(0).expect("sign operator should be in + or -"), proc_macro2::Spacing::Alone).to_token_stream();
                    // }
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    result_unwrapped = true;
                    let asserts = quote::quote! {ret == #sign #ret1};
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::Symmetry,
                        asserts,
                        "f(x) = ±f(2*y - x)",
                        &desc.clone(),
                    );
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #assert_stream
                    }
                }
                (ContractType::Homomorphism, _) => {
                    let third_run_index = mr_info.retindex2;
                    // let op = c.streams[1].clone();
                    let ret2 = syn::Ident::new(format!("{}{}", "ret", third_run_index).as_str(), span);
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    let ret2_unwrap = unwrap_return(ret_type, &ret2);
                    let a = merge_expr(ret_type, &ret_str_ident, &ret1.to_token_stream(), &op);
                    let asserts = quote::quote! {#a == #ret2};
                    // let asserts = quote::quote! {ret == #ret1 + #ret2};
                    result_unwrapped = true;
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::Homomorphism,
                        asserts,
                        "f(x) + f(y) = f(x + y)",
                        &desc.clone(),
                    );
                    quote::quote! {
                        #ret0_unwrap
                        #ret1_unwrap
                        #ret2_unwrap
                        #assert_stream
                    }
                }
                (ContractType::IterConsistency, _) => {
                    let para = syn::Ident::new(format!("{}{}", mr_info.variable_name, "_contract_old").as_str(), span);
                    op = c.streams[1].clone();
                    // let op = c.streams[1].clone();
                    // let a = merge_expr(ret_type, &ret_str_ident, &ret_str_ident, &op);
                    // let b = merge_expr(ret_type, &ret1, &para, &op);
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    let a = merge_expr(ret_type, &ret1, &ret_str_ident.to_token_stream(), &op);
                    let b = merge_expr(ret_type, &ret_str_ident, &para.to_token_stream(), &op);
                    let asserts = quote::quote! {#a == #b};
                    // let asserts = quote::quote! {ret + ret == #ret1 + #para};
                    result_unwrapped = true;
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::IterConsistency,
                        asserts,
                        "f(f(x)) - f(x) = f(x) - x",
                        &desc.clone(),
                    );
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #assert_stream
                    }
                }
                (ContractType::Monotonicity, _) => {
                    // let asserts = quote::quote! {#a};
                    if extra_op.is_empty(){
                        println!("Dimension transformation require three arguments, op, modi, second_op");
                        return extra_op;
                    };
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    result_unwrapped = true;
                    let asserts = merge_expr(ret_type, &ret_str_ident, &ret1.to_token_stream(), &extra_op);
                    // asserts = quote::quote! {ret #extra_op #ret1};
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::Monotonicity,
                        asserts,
                        "x < y -> f(x) < f(y)",
                        &desc.clone(),
                    );
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #assert_stream
                    }
                }
                (ContractType::Mapping, _) => {
                    let third_run_index = mr_info.retindex2;
                    if extra_op.is_empty(){
                        println!("Dimension transformation require three arguments, op, modi, second_op");
                        return extra_op;
                    };
                    let ret2 = syn::Ident::new(format!("{}{}", "ret", third_run_index).as_str(), span);
                    if ! result_unwrapped{
                        ret0_unwrap = unwrap_return(ret_type, &ret_str_ident);
                    }
                    let ret1_unwrap = unwrap_return(ret_type, &ret1);
                    let ret2_unwrap = unwrap_return(ret_type, &ret2);
                    let a = merge_expr(ret_type, &ret1, &ret_str_ident.to_token_stream(), &extra_op);
                    let b = merge_expr(ret_type, &ret2, &ret1.to_token_stream(), &extra_op);
                    let asserts = quote::quote! {#a == #b};
                    result_unwrapped = true;
                    let assert_stream = make_str_assertion(
                        mode,
                        ContractType::Mapping,
                        asserts,
                        "f(x + y) - f(x) = f(x + 2y) - f(x + y)",
                        &desc.clone(),
                    );
                    quote::quote! { 
                        #ret0_unwrap 
                        #ret1_unwrap
                        #ret2_unwrap
                        #assert_stream
                    }
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
    // println!("{:?}", run_map);
    // println!("{:?}", index);

    // clone the mut para
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
    // println!("clone def: {}", clone_mut);
        
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
    // println!("original body: {}", perpare_and_body);

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
                let key = &mr_info.variable.to_string();
                let para1 = syn::Ident::new(format!("{}{}{}", mr_info.variable.to_string(), "_contract_", second_run_index).as_str(), span);
                let mut mutstr = TokenStream::new(); 
                if mut_para.contains(key){
                    mutstr = quote::quote! { mut };
                }
                quote::quote! {
                    let #mutstr #para1 = ret.clone();
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
                        let mut parareplace = ParaReplace{new_para: format!(" {}{}{} ", keyclone, "_contract_", second_run_index), old_para: keyclone.clone()};
                        let mut expr_clone = expr.clone();
                        let ex = &mut expr_clone;
                        parareplace.visit_expr_mut(ex);
                        println!("{}", ex.to_token_stream().to_string());
                        // let expr = expr.into_token_stream().to_string().replace(
                        //     format!("{}", keyclone).as_str(), format!(" {}{}{} ", keyclone, "_contract_", second_run_index).as_str());
                        // // expr = expr.replace("\n", "");
                        // let expr_result = syn::parse_str::<Expr>(expr.as_str());
                        // let expr = match expr_result{
                        //     Ok(expr) => expr,
                        //     Err(e) => {
                        //         println!("{}", expr);
                        //         println!("{}", e);
                        //         panic!("wrong construction of pre-condition for extra run body.");
                        //     },
                        // };
                        make_assertion(
                            mode,
                            ContractType::Requires,
                            display.clone(),
                            &ex,
                            &desc.clone(),
                        )
                    },
                )
            })
            .collect();
        // println!("pre for clone: {:?}", preforclone);

        let block_attrs = func.function
                .block.clone();

        // let block_attrs_string = block_attrs.to_token_stream().to_string();
        // println!("{}", block_attrs_string);
        
        let mut block_attrs = syn::parse2::<Expr>(block_attrs.to_token_stream()).expect("function body does not pass compiler");
        // println!("{:?}", block_attrs);
        for para in &mut_para1{
            // block_attrs = block_attrs.replace(format!("* {}", para).as_str(), format!(" {} ", para).as_str());
            let mut parareplace = ParaReplace { new_para: format!("{}{}{}", para, "_contract_", second_run_index), old_para: para.clone() };
            parareplace.visit_expr_mut(&mut block_attrs);
        }

        // block_attrs = block_attrs.replace(format!("* {}", key).as_str(), format!(" {} ", key).as_str());
        let mut parareplace = ParaReplace { new_para: format!("{}{}{}", key, "_contract_", second_run_index), old_para: key.clone() };
        parareplace.visit_expr_mut(&mut block_attrs);
        // block_attrs = block_attrs.replace("\n", "");
        // let block_attrs = syn::parse_str::<Expr>(block_attrs.as_str()).expect("function body does not pass compiler");
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
            ContractType::Homomorphism | ContractType::Mapping => {
                one_extra_run(second_run_index);
                one_extra_run(second_run_index + 1);
            },
            _ => one_extra_run(second_run_index),
        };
    }

    let mut ret_pack:TokenStream = quote::quote! {ret};
    if result_unwrapped{
        let ret_type = variable_type.get(&String::from("ret")).unwrap().as_str();
        ret_pack = match ret_type{
            "Result" => quote::quote! {Ok(ret)},
            "Option" => quote::quote! {Some(ret)},
            _ => quote::quote! {ret},
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

            #ret_pack
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

fn merge_statement(ident_type: &str , para: &syn::Ident, modi: &TokenStream, 
    op: &TokenStream, mut_def: &TokenStream, para_clone: &syn::Ident) -> TokenStream {
    let op_tokenstream:proc_macro2::TokenStream = syn::parse2(op.clone()).expect("operator not loaded correctly");
    let mut op_type = syn::parse_str("+").unwrap();
    for token in op_tokenstream{
        match token{
            proc_macro2::TokenTree::Punct(_) =>(),
            proc_macro2::TokenTree::Ident(_) =>{op_type = token; break;},
            _ => {println!("invalid operator {}, use default operator", op);
            break;
            },
        };
    }
    match (ident_type, op_type){
        ("str", proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            // (#para.to_string().push_str(#modi)).as_str()
            let #mut_def #para_clone = format!("{}{}", #para.to_string(),#modi.to_string());
            let #mut_def #para_clone = #para_clone.as_str();
        },
        ("String",proc_macro2::TokenTree::Punct(_)) => {
            quote::quote! {
                let #mut_def #para_clone = #para.clone()#op#modi;
            }
        },
        ("sym_float",_) => quote::quote! {
            let #mut_def #para_clone = (2.0 * #modi) #op #para;
        },
        ("sym_number",_) => quote::quote! {
            let #mut_def #para_clone = (2 * #modi) #op #para;
        },
        ("sym_bool",_) => quote::quote! {
            let #mut_def #para_clone = !(#para.clone());
        },
        ("sym_func", proc_macro2::TokenTree::Punct(_)) =>quote::quote! {
            let #mut_def #para_clone = #modi #op #para.clone();
        },
        ("sym_func",_) => quote::quote! {
            let mut #para_clone = #para.clone();
            let #mut_def #para_clone = #para_clone.#op();
        },
        (_,proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            let #mut_def #para_clone = #para.clone()#op#modi;
        },
        (_ ,_)=>quote::quote! {
            let mut #para_clone = #para.clone();
            let #mut_def #para_clone = #para_clone.#op(#modi);
        },
    }
}

fn unwrap_return(ident_type: &str, para: &syn::Ident) -> TokenStream {
    let para_token_stream = para.to_token_stream();
    match ident_type{
        "Option" =>{
            quote::quote! {
                let #para_token_stream = #para_token_stream .unwrap();
            }
        },
        "Result" =>{
            quote::quote! {
                let #para_token_stream = #para_token_stream .unwrap();
            }
        },
        _ => TokenStream::new(),
    }
}

fn merge_expr(ident_type: &str , para: &syn::Ident, modi: &TokenStream, op: &TokenStream) -> TokenStream {
    let op_tokenstream:proc_macro2::TokenStream = syn::parse2(op.clone()).expect("operator not loaded correctly for expression");
    let mut op_type = syn::parse_str("+").unwrap();
    for token in op_tokenstream{
        match token{
            proc_macro2::TokenTree::Punct(_) =>(),
            proc_macro2::TokenTree::Ident(_) =>{op_type = token; break;},
            _ => {println!("invalid operator{}, use default operator", op);
            break;
            },
        };
    }
    // println!("{}{}{}", para, op, modi);
    // let para = match ident_type{
    //     "Result" =>{quote::quote! {
    //         #para .clone().unwrap()
    //     }
    //     },
    //     "Option" =>{
    //         quote::quote! {
    //             #para .clone().unwrap()
    //         }
    //     },
    //     _ =>para.to_token_stream(),
    // };
    // let second_ret = modi.clone().to_string();
    // let mut modi = modi.to_token_stream();
    // if ! second_ret.contains("contract_old") {
    //     modi = match ident_type{
    //         "Option" =>{
    //             quote::quote! {
    //                 #modi .unwrap()
    //             }
    //         },
    //         "Result" =>{
    //             quote::quote! {
    //                 #modi .unwrap()
    //             }
    //         },
    //         _ => modi,
    //     };
    // }
    
    match (ident_type,op_type){
        ("str", proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            format!("{}{}", #para.to_string(),#modi.to_string()).as_str()
        },
        ("String",proc_macro2::TokenTree::Punct(_)) => {
            quote::quote! {
                format!("{}{}", #para,#modi).as_str()
            }
        },
        (_,proc_macro2::TokenTree::Punct(_)) => quote::quote! {
            #para.clone()#op#modi.clone()
        },
        (_ ,proc_macro2::TokenTree::Ident(_))=>quote::quote! {
             #para.clone().#op(#modi.clone())
        },
        (_,_) => panic!("should never reach"),
    }
}
