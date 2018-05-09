## μgie: robustness testing of Boogie
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

## Benchmark Mutants: 
Our benchmarking seeds can be found under `/seeds`

Directory [`experiments`](experiments/) includes the experimental data in CSV format.
 
## [μgie website](http://emptylambda.github.io/mu-gie/)
Just in case you arrived here without seeing the intro webpage :) 
