## μgie: robustness testing of Boogie programs
μgie is a tool to perform _robustness testing_ of programs written in the popular intermediate verification language [Boogie](https://github.com/boogie-org/boogie).

Given a Boogie program as input, μgie generates many syntactic *mutants* that are constructed to be semantically equivalent to the input.
If Boogie behaves differently with some of the mutants (namely, it verifies successfully the input program but fails to verify some of the mutants), it means that Boogie's behavior is *brittle* on that particular example, because it depends on minor syntactic details that should be immaterial.

## Usage

To run μgie:
```shell
$ BMu config.json
```
where `config.json` is a JSON configuration file that specifies:
  * `sourceBoogie`: input Boogie program to mutate
  * `mutationRatio`: weights of mutation operators (determining the likelihood of randomly selecting each operator)
  * `numberOfMutants`: number of mutants to generate
  * `mutationAttempts`: number of attempts to generate new mutants
  * `outputToFile`: output to files (default: output to standad output)
  * `verbose`: verbose output during generation
  * `prefix`: add a prefix to all generated mutants
  * `mutationLevels`: how many mutation operators are generated internally (this is for debugging purposes)
  
We include an example `config.json` under the `Mutation` directory, which only uses the "L8" mutation operator and generates 1 mutant with at most 10000 tries.

## Details and experiments
Details about robustness testing, μgie, and an experimental evaluation are available in the paper [Robustness testing of intermediate verifiers](https://arxiv.org/abs/XXXX.XXXXX).


## Mutation operators
------------------
The implementation of μgie includes more mutation operators than those described in the paper, and the operators' names are not the same as those used in the paper:

| operator name in the paper | operator name in μgie |
|:--------------------------:|:---------------------:|
| S1                         | S1                    |
| S2                         | S5                    |
| S3                         | S6                    |
| L1                         | L1                    |
| L2                         | L2                    |
| L3                         | L4                    |
| L4                         | L5                    |
| L5                         | L6                    |
| L6                         | L8                    |
| G1                         | G1                    |
| G2                         | G2                    |


Here is a table briefly describing each mutation operator: 

| operator name in μgie | description                                                                        |
|:---------------------:|:----------------------------------------------------------------------------------:|
| S1                    | Swap any two declarations                                                          |
| S5                    | Split a procedure definition into declaration and implementation                   |
| S6                    | Move any declaration into a separate file (and call Boogie on both files)          |
| L1                    | Swap any two *local* variable declarations                                         |
| L2                    | Split a declaration of multiple variables into multiple declarations               |
| L4                    | Join any two preconditions into a conjunctive one                                  |
| L5                    | Join any two postconditions into a conjunctive one                                 |
| L6                    | Swap the oder of pre-/postconditions                                               |
| L8                    | Negate `if` condition and flip its two branches                                    |
| G1                    | Add `true` as pre-/postcondition, intermediate assertion, or loop invariant clause |
| G2                    | Remove trigger annotation                                                          |


## Headers
Each mutant includes a header comment with information about 
how the mutant was generated as a sequence of application of
mutations operators to the original input Boogie program.
