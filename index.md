## μgie : intemediate verification testing

We call this approach the robustness testing of verifiers. 

μgie inputs a seed [Boogie program](https://github.com/boogie-org/boogie) and generates a collection of mutant programs, each with a slight mutation twist from original seed. These mutations do not introduce any semantical change to the underlying seed but merely explore syntatical variants of the seed, think of it as a "thesaursus" for your Boogie programs. 


## Usage 
TBD 

## Current mutations: 
| Mutation Name                   | Mutation Code   | description                                                                                                                                                                                                                                 |
| --------------                  | --------------- | -----------                                                                                                                                                                                                                                 |
| Swapping Declarations           | S1              | swapping two randomly selected declarations from the seed program; according to Boogie documentation the declaration order should be immaterial! but according to our preliminary study, 50% of the permutations can lead to proof failure. |
| Axiomatize function definitions | S2              |                                                                                                                                                                                                                                             |


## Benchmark programs: 
TBD 

<!-- Whenever you commit to this repository, GitHub Pages will run [Jekyll](https://jekyllrb.com/) to rebuild the pages in your site, from the content in your Markdown files. -->

<!-- ### Markdown -->

<!-- Markdown is a lightweight and easy-to-use syntax for styling your writing. It includes conventions for -->

<!-- ```markdown -->
<!-- Syntax highlighted code block -->

<!-- # Header 1 -->
<!-- ## Header 2 -->
<!-- ### Header 3 -->

<!-- - Bulleted -->
<!-- - List -->

<!-- 1. Numbered -->
<!-- 2. List -->

<!-- **Bold** and _Italic_ and `Code` text -->

<!-- [Link](url) and ![Image](src) -->
<!-- ``` -->

<!-- For more details see [GitHub Flavored Markdown](https://guides.github.com/features/mastering-markdown/). -->

<!-- ### Jekyll Themes -->

<!-- Your Pages site will use the layout and styles from the Jekyll theme you have selected in your [repository settings](https://github.com/emptylambda/mu-gie/settings). The name of this theme is saved in the Jekyll `_config.yml` configuration file. -->

<!-- ### Support or Contact -->

<!-- Having trouble with Pages? Check out our [documentation](https://help.github.com/categories/github-pages-basics/) or [contact support](https://github.com/contact) and we’ll help you sort it out. -->
