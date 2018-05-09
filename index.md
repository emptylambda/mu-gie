## μgie: robustness testing of intemediate verifiers

μgie inputs a seed [Boogie program](https://github.com/boogie-org/boogie) and generates a collection of mutant programs, each with a slight mutation twist from original seed. These mutations do not introduce any semantical change to the underlying seed but merely explore syntatical variants of it: think of μgie as a "thesaursus" for your Boogie programs.

See the [README](README.md) file for details.
