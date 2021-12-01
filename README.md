# *Design By Contract* for Rust

Annotate functions and methods with "contracts", using *invariants*,
*pre-conditions* and *post-conditions*.

[Design by contract][dbc] is a popular method to augment code with formal
interface specifications.
These specifications are used to increase the correctness of the code by
checking them as assertions at runtime.

[dbc]: https://en.wikipedia.org/wiki/Design_by_contract

```rust
pub struct Library {
    available: HashSet<String>,
    lent: HashSet<String>,
}

impl Library {
    fn book_exists(&self, book_id: &str) -> bool {
        self.available.contains(book_id)
            || self.lent.contains(book_id)
    }

    #[debug_requires(!self.book_exists(book_id), "Book IDs are unique")]
    #[debug_ensures(self.available.contains(book_id), "Book now available")]
    #[ensures(self.available.len() == old(self.available.len()) + 1)]
    #[ensures(self.lent.len() == old(self.lent.len()), "No lent change")]
    pub fn add_book(&mut self, book_id: &str) {
        self.available.insert(book_id.to_string());
    }

    #[debug_requires(self.book_exists(book_id))]
    #[ensures(ret -> self.available.len() == old(self.available.len()) - 1)]
    #[ensures(ret -> self.lent.len() == old(self.lent.len()) + 1)]
    #[debug_ensures(ret -> self.lent.contains(book_id))]
    #[debug_ensures(!ret -> self.lent.contains(book_id), "Book already lent")]
    pub fn lend(&mut self, book_id: &str) -> bool {
        if self.available.contains(book_id) {
            self.available.remove(book_id);
            self.lent.insert(book_id.to_string());
            true
        } else {
            false
        }
    }

    #[debug_requires(self.lent.contains(book_id), "Can't return a non-lent book")]
    #[ensures(self.lent.len() == old(self.lent.len()) - 1)]
    #[ensures(self.available.len() == old(self.available.len()) + 1)]
    #[debug_ensures(!self.lent.contains(book_id))]
    #[debug_ensures(self.available.contains(book_id), "Book available again")]
    pub fn return_book(&mut self, book_id: &str) {
        self.lent.remove(book_id);
        self.available.insert(book_id.to_string());
    }
}
```

## Attributes

This crate exposes the `requires`, `ensures` and `invariant` attributes.

- `requires` are checked before a function/method is executed.
- `ensures` are checked after a function/method ran to completion
- `invariant`s are checked both before *and* after a function/method ran.

Additionally, all those attributes have versions with different "modes". See
[the Modes section](#Modes) below.

For `trait`s and trait `impl`s the `contract_trait` attribute can be used.

More specific information can be found in the crate documentation.

## Pseudo-functions and operators

### `old()` function

One unique feature that this crate provides is an `old()` pseudo-function which
allows to perform checks using a value of a parameter before the function call
happened. This is only available in `ensures` attributes.

```rust
#[ensures(*x == old(*x) + 1, "after the call `x` was incremented")]
fn incr(x: &mut usize) {
    *x += 1;
}
```

### `->` operator

For more complex functions it can be useful to express behaviour using logical
implication. Because Rust does not feature an operator for implication, this
crate adds this operator for use in attributes.

```rust
#[ensures(person_name.is_some() -> ret.contains(person_name.unwrap()))]
fn geeting(person_name: Option<&str>) -> String {
    let mut s = String::from("Hello");
    if let Some(name) = person_name {
        s.push(' ');
        s.push_str(name);
    }
    s.push('!');
    s
}
```

This operator is right-associative.

**Note**: Because of the design of `syn`, it is tricky to add custom operators
to be parsed, so this crate performs a rewrite of the `TokenStream` instead.
The rewrite works by separating the expression into a part that's left of the
`->` operator and the rest on the right side. This means that
`if a -> b { c } else { d }` will not generate the expected code.
Explicit grouping using parenthesis or curly-brackets can be used to avoid this.


## Modes

All the attributes (requires, ensures, invariant) have `debug_*` and `test_*` versions.

- `debug_requires`/`debug_ensures`/`debug_invariant` use `debug_assert!`
  internally rather than `assert!`
- `test_requires`/`test_ensures`/`test_invariant` guard the `assert!` with an
  `if cfg!(test)`.
  This should mostly be used for stating equivalence to "slow but obviously
  correct" alternative implementations or checks.
  
  For example, a merge-sort implementation might look like this
  ```rust
  #[test_ensures(is_sorted(input))]
  fn merge_sort<T: Ord + Copy>(input: &mut [T]) {
      // ...
  }
  ```

## Set-up

To install the latest version, add `contracts` to the dependency section of the
`Cargo.toml` file.

```
[dependencies]
contracts = your path to the contract directory
```

To then bring all procedural macros into scope, you can add `use contracts::*;`
in all files you plan to use the contract attributes.

Alternatively use the "old-style" of importing macros to have them available
project-wide.

```rust
#[macro_use]
extern crate contracts;
```

## Todo
-- all mr related defination and explanation.

The default contract all involves only one execution of the function. But some function invariant occurs when the function is continuous called. So we purpose the contract with the metamorphic relation to generate more widely used function contracts.
There are six metamorphic relation that we define in parameter list form. The name could reflect the meaning of them.

![image](https://user-images.githubusercontent.com/29123294/144240554-665cce08-6ab3-4f03-8c83-48a58081a120.png)

just a defination example, the function does not actual follow the relation.

```
#[symmetry(book_id, -, 1, +, "my symmetry test")]
#[monotonicity(book_id, +, 1, <=, "my monotonicity test")]
#[homomorphism(book_id, +, 1, "my homomorphism test")]
#[periodicity(book_id, +, 1, "my cyclicity test")]
#[dimension_trans(book_id, +, 1, +, "my add equal test")]
pub fn add_book(&mut self, mut book_id: usize, a:usize) -> usize
{
    book_id =a+book_id;
    self.available.insert((book_id + 1).to_string());
    self.available.len()
}
```

To explain, the first parameter (changing variable) could be a struct and should be in the function inputs, the second parameter (operator) could be function, and the third parameter (variation) could be a valid expression. So the defination of metamorphosis change are not limited in numeric arithmatic.

Yet another example
```
#[debug_requires(self.lent.contains(&book.id.to_string()), "Can't return a non-lent book")]
#[ensures(self.lent.len() == old(self.lent.len()) - 1)]
#[symmetry(book, reverse, a, +, "my symmetry test")]
#[iter_consistency(book, merge, "my iter consistency test")]
#[monotonicity(book, add, 1, cmp, "my monotonicity test")]
#[homomorphism(book, merge, Book{id:1, author:String::from("bad boy")}, "my homomorphism test")]
#[periodicity(book, add, 1, "my cyclicity test")]
#[periodicity(book, +, 1, "my cyclicity test")]
#[mapping(book, add, 1, merge, "my cyclicity test")]
pub fn destory_book(&mut self, book: Book) -> Book{
    # something to do
}
```

As you can see, our metamorphic contract can be used aggregately as above, and it can be used with original contract.

To better define your contract, we allow users to define expressions freely. The contract type name is `mr`. Let introduce with an example.
```
#[mr(add_book(book_id + 1).add(add_book(a + 2, book_id + a + 1)) == add_book(self, a))]
pub fn add_book(&mut self, mut book_id: usize, a:usize) -> usize
{
    # something to do
}
```
This relation involves three execution of the function, the first change the `book_id`, while the second change the `book_id` and `a`. The third one is a invariant version of the function.

This kind of defination allow many unsatisifable relation before. You can use multiply variable, variation, function. Also it allows you to define your own judgement function for example, floating point equivalence to avoid floating point precision loss. But you have to make sure the expression is valid.

To generate the oracle for the function with exception or condition, you could use the if-condition expression to forbid the check for certain input field. The last example:
```
#[mr(if book_id > 0 {add_book(book_id + 1).add(add_book(a + 2, book_id + a + 1)) == add_book(self, book_id, a)})]
pub fn add_book(&mut self, mut book_id: usize, a:usize) -> usize
{
    # something to do
}
```

Having fun with the metamorphic relation contracts hunting.
