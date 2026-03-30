# Generator Creation Workflow

Basalt provides a foundation for provably correct and efficient data generators. It can be used in
conjunction with property-based testing frameworks in Lean and other languages to find a wide range
of bugs in code.

This file provides a workflow for creating your own generator and proving it correct.

## Basic Workflow

### Step 0: Choose a Data Type

Determine a type `α` of data that you would like to generate. If you are generating data for
consumption by another language, you will likely want to make a bespoke inductive data type in Lean
that mirrors your data structures in your implementation language.

### Step 1: Define Validity

Determine what it means for your data to be _valid_. This should be a predicate `P` of type `α →
Prop`, and `P a` should be `True` iff `a` is a valid input to your system under test.

Advanced users might want to target specific sub-spaces of their data type for testing (e.g.,
well-typed programs vs. ill-typed but well-scoped programs). In that case, we recommend going
through this process multiple times for each sub-space, rather than trying to do all sub-spaces at
once.

### Step 2: Set a Cost Bound

Determine a reasonable cost bound for generation. Generally this will be based on the size of the
data structure you are generating (e.g., when generating lists, the bound will often be proportional
to the length of the list). Specifically, the will be used to bound the number of random choices
that are made when producing a given value.

We recommend that you keep this bound relatively tight: requiring a precise bound reduces the chance
that the generator you end up with does backtracking search or some other inefficient computation
during generation.

### Step 3: Create and Validate Your Generator

Create a generator of the appropriate type. For example:
```lean
def myGen [Gen G] : G α := ...
```
We use a type-class embedding of generators because it works well with our proof infrastructure. See
the `Gen.lean` file for more.

Once your generator is done, prove the appropriate instance for `LawfulGenerator`. The type-class is
parameterized by a validity predicate and a cost, which you should set based on your previous
choices.

## Tips and Tricks

- Do not use a dependent type for your base type `α`. Instead, rely on your validity predicate to
  constrain the data.
- If you're not sure what cost bound to use, try writing the generator first and then determining a
  reasonable bound. If you find you can't come up with a bound after writing your generator, you may
  have made some inefficient choices and might consider rethinking your approach.