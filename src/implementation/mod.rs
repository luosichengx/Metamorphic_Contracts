/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub(crate) mod codegen;
pub(crate) mod doc;
pub(crate) mod ensures;
pub(crate) mod invariant;
pub(crate) mod parse;
pub(crate) mod requires;
pub(crate) mod traits;
pub(crate) mod periodicity;
pub(crate) mod add_not_equal;
pub(crate) mod local_invariance;
pub(crate) mod iterconsistency;
pub(crate) mod homomorphism;
pub(crate) mod symmetry;
pub(crate) mod monotonicity;
pub(crate) mod mapping;

use quote::ToTokens;
use syn::{Expr, ItemFn};

pub(crate) use ensures::ensures;
pub(crate) use invariant::invariant;
use proc_macro2::{Span, TokenStream, TokenTree};
pub(crate) use requires::requires;
pub(crate) use periodicity::periodicity;
pub(crate) use mapping::mapping;
pub(crate) use add_not_equal::add_not_equal;
pub(crate) use local_invariance::local_invariance;
pub(crate) use iterconsistency::iter_consistency;
pub(crate) use homomorphism::homomorphism;
pub(crate) use symmetry::symmetry;
pub(crate) use monotonicity::monotonicity;
pub(crate) use traits::{contract_trait_item_impl, contract_trait_item_trait};

/// Checking-mode of a contract.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum ContractMode {
    /// Always check contract
    Always,
    /// Never check contract
    Disabled,
    /// Check contract only in debug builds
    Debug,
    /// Check contract only in `#[cfg(test)]` configurations
    Test,
    /// Check the contract and print information upon violation, but don't abort
    /// the program.
    LogOnly,
}

impl ContractMode {
    /// Return the prefix of attributes of `self` mode.
    pub(crate) fn name(self) -> Option<&'static str> {
        match self {
            ContractMode::Always => Some(""),
            ContractMode::Disabled => None,
            ContractMode::Debug => Some("debug_"),
            ContractMode::Test => Some("test_"),
            ContractMode::LogOnly => None,
        }
    }

    /// Computes the contract type based on feature flags.
    pub(crate) fn final_mode(self) -> Self {
        // disabled ones can't be "forced", test ones should stay test, no
        // matter what.
        if self == ContractMode::Disabled || self == ContractMode::Test {
            return self;
        }

        if cfg!(feature = "disable_contracts") {
            ContractMode::Disabled
        } else if cfg!(feature = "override_debug") {
            // log is "weaker" than debug, so keep log
            if self == ContractMode::LogOnly {
                self
            } else {
                ContractMode::Debug
            }
        } else if cfg!(feature = "override_log") {
            ContractMode::LogOnly
        } else {
            self
        }
    }
}

/// The different contract types.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum ContractType {
    Requires,
    Ensures,
    Invariant,
    Periodicity,
    AddNotEqual,
    LocalInvariance,
    Monotonicity,
    Symmetry,
    Homomorphism,
    IterConsistency,
    Mapping,
}

impl ContractType {
    /// Get the name that is used as a message-prefix on violation of a
    /// contract.
    pub(crate) fn message_name(self) -> &'static str {
        match self {
            ContractType::Requires => "Pre-condition",
            ContractType::Ensures => "Post-condition",
            ContractType::Invariant => "Invariant",
            ContractType::Periodicity => "periodicity",
            ContractType::AddNotEqual => "add_not_equal",
            ContractType::LocalInvariance => "local_invariance",
            ContractType::Monotonicity => "monotonicity",
            ContractType::Symmetry => "symmetry",
            ContractType::Homomorphism => "homomorphism",
            ContractType::IterConsistency => "iter_consistency",
            ContractType::Mapping => "mapping",
        }
    }

    /// Determine the type and mode of an identifier.
    pub(crate) fn contract_type_and_mode(
        ident: &str,
    ) -> Option<(ContractType, ContractMode)> {
        match ident {
            "requires" => Some((ContractType::Requires, ContractMode::Always)),
            "ensures" => Some((ContractType::Ensures, ContractMode::Always)),
            "invariant" => {
                Some((ContractType::Invariant, ContractMode::Always))
            }
            "debug_requires" => {
                Some((ContractType::Requires, ContractMode::Debug))
            }
            "debug_ensures" => {
                Some((ContractType::Ensures, ContractMode::Debug))
            }
            "debug_invariant" => {
                Some((ContractType::Invariant, ContractMode::Debug))
            }
            "test_requires" => {
                Some((ContractType::Requires, ContractMode::Test))
            }
            "test_ensures" => Some((ContractType::Ensures, ContractMode::Test)),
            "test_invariant" => {
                Some((ContractType::Invariant, ContractMode::Test))
            }
            "periodicity" => Some((ContractType::Periodicity, ContractMode::Test)),
            "add_not_equal" => Some((ContractType::AddNotEqual, ContractMode::Test)),
            "local_invariance" => Some((ContractType::LocalInvariance, ContractMode::Test)),
            "monotonicity" => Some((ContractType::Monotonicity, ContractMode::Test)),
            "symmetry" => Some((ContractType::Symmetry, ContractMode::Test)),
            "homomorphism" => Some((ContractType::Homomorphism, ContractMode::Test)),
            "iter_consistency" => Some((ContractType::IterConsistency, ContractMode::Test)),
            "mapping" => Some((ContractType::Mapping, ContractMode::Test)),
            _ => None,
        }
    }
}

/// Representation of a contract
#[derive(Debug)]
pub(crate) struct Contract {
    pub(crate) span: Span,
    pub(crate) ty: ContractType,
    pub(crate) mode: ContractMode,
    pub(crate) assertions: Vec<Expr>,
    pub(crate) streams: Vec<TokenStream>,
    pub(crate) desc: Option<String>,
}

impl Contract {
    pub(crate) fn from_toks(
        ty: ContractType,
        mode: ContractMode,
        toks: TokenStream,
    ) -> Self {
        let (assertions, streams, desc) = parse::parse_attributes(toks);

        let span = Span::call_site();

        Self {
            span,
            ty,
            mode,
            assertions,
            streams,
            desc,
        }
    }
}

/// A function that is annotated with contracts
#[derive(Debug)]
pub(crate) struct FuncWithContracts {
    pub(crate) contracts: Vec<Contract>,
    pub(crate) function: ItemFn,
}

impl FuncWithContracts {
    /// Create a `FuncWithContracts` value from the attribute-tokens of the
    /// first contract and a parsed version of the function.
    ///
    /// The initial contract is parsed from the tokens, others will be read from
    /// parsed function.
    pub(crate) fn new_with_initial_contract(
        mut func: ItemFn,
        cty: ContractType,
        cmode: ContractMode,
        ctoks: TokenStream,
    ) -> Self {
        // add in the first attribute
        let mut contracts: Vec<Contract> = {
            let initial_contract = Contract::from_toks(cty, cmode, ctoks);
            vec![initial_contract]
        };

        // find all other attributes

        let contract_attrs = func
            .attrs
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().unwrap().ident.to_string();
                let (ty, mode) = ContractType::contract_type_and_mode(&name)?;
                Some((ty, mode, a))
            })
            .map(|(ty, mode, a)| {
                // the tts on attributes contains the out parenthesis, so some
                // code might be mistakenly parsed as tuples, that's not good!
                //
                // this is a hack to get to the inner token stream.

                let tok_tree = a.tokens.clone().into_iter().next().unwrap();
                let toks = match tok_tree {
                    TokenTree::Group(group) => group.stream(),
                    TokenTree::Ident(i) => i.into_token_stream(),
                    TokenTree::Punct(p) => p.into_token_stream(),
                    TokenTree::Literal(l) => l.into_token_stream(),
                };

                Contract::from_toks(ty, mode, toks)
            });

        contracts.extend(contract_attrs);

        // remove contract attributes
        {
            let attrs = std::mem::replace(&mut func.attrs, vec![]);

            let other_attrs = attrs
                .into_iter()
                .filter(|attr| {
                    ContractType::contract_type_and_mode(
                        &attr.path.segments.last().unwrap().ident.to_string(),
                    )
                    .is_none()
                })
                .collect();

            func.attrs = other_attrs;
        }

        Self {
            function: func,
            contracts,
        }
    }

    /// Generates the resulting tokens including all contract-checks
    pub(crate) fn generate(mut self) -> TokenStream {
        let doc_attrs = doc::generate_attributes(&self.contracts);
        let olds = codegen::extract_old_calls(&mut self.contracts);

        codegen::generate(self, doc_attrs, olds)
    }
}
