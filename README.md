## μgie: lightweight testing on [Boogie](https://github.com/boogie-org/boogie)
μgie provides a lightweight testing on the popular intermediate verification language Boogie. 
We call this idea the _robustness testing_ on IVLs.  
By introducing syntactical variants (which should not impose any semantical change), μgie generates a collection of mutants from the input seed program.  
The goal of mutating the original seed Boogie program is to exercise possible language variants of Boogie, and to further explore brittle behaviours of deductive verification systems.  

## Usage: 
μgie operates by reading a stand-alone JSON configuration file.  
You can invoke μgie by:  `BMu config.json`
Inside the JSON config file you can specify the following parameters: 
  1. `sourceBoogie`: source program you want to conduct robustness testing. 
  2. `mutationRatio`: deciding the overall distribution of each mutation operator; the randomly operator selection is based on this weighted list. 
  3. `mutationLevels`: specifying how many _mutation operators_ are generated internally; mainly for internal testing and is a refined parameter. 
  4. `numberOfMutants`: #mutants you wish to output. 
  5. `mutationAttempts`: #tries before giving up. 
  6. `outputToFile`: if μgie should write to STDOUT or to files. 
  7. `verbose`: toggle verbose output along the generation process. 
  8. `prefix`: adding a customized prefix on the generated mutants. 
  
We've included on example `config.json` under `Mutation` directory, it is configured to: only use "L8" as mutation operator and generate 1 mutant within 10000 tries. The mutant is reported to STDOUT. 

## Benchmark Mutants: 
Here's a collection of mutants we used as our [benchmark](https://chalmersuniversity.box.com/shared/static/5a1dvt1s0am5smx4u23oezuw6633hiuf.zip), including an un-biased mutant set and specialized ones. 


## [μgie website](http://emptylambda.github.io/mu-gie/)
Just in case you arrive here without seeing the intro webpage :) 
