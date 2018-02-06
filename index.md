## μgie : intemediate verification testing

We call this approach the robustness testing of verifiers. 

μgie inputs a seed [Boogie program](https://github.com/boogie-org/boogie) and generates a collection of mutant programs, each with a slight mutation twist from original seed. These mutations do not introduce any semantical change to the underlying seed but merely explore syntatical variants of the seed, think of it as a "thesaursus" for your Boogie programs. 


## Usage 
TBD 

## Current mutations: 


## Benchmark programs: 
Our benchmark programs used in the paper can be found [here](https://chalmersuniversity.box.com/shared/static/5a1dvt1s0am5smx4u23oezuw6633hiuf.zip) (*Notice the entire benchmark is around 3.8Gb after decompression) 

<!-- | Mutation Name                   | Mutation Code   | description                                                                                                                                                                                                                                 | -->
<!-- | --------------                  | --------------- | -----------                                                                                                                                                                                                                                 | -->
<!-- | Swapping Declarations           | S1              | swapping two randomly selected declarations from the seed program; according to Boogie documentation the declaration order should be immaterial! but according to our preliminary study, 50% of the permutations can lead to proof failure. | -->
<!-- | Axiomatize function definitions | S2              |                                                                                                                                                                                                                                             | -->

