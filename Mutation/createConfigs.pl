#!/usr/bin/perl
use strict;
use warnings;
use Cwd;


opendir my $dir, getcwd() or die "cannot open directory";
my @cores = readdir $dir;
my $filename = 'config.json';
foreach my $core (@cores){
    # if ($sub =~/group/) {
	# print $sub . "\n"; #Lab2 PartB ($sub)\n #$fh 
	# open (my $fh, '>', "./$sub/$filename") or die "Failed to open file $filename"; 
	print 
"{
	\"sourceBoogie\":\"./test/BoogieProgram/($core).bpl\", 
";

	## statics
# 	print $fh 
# "

# ";
# 	close $fh;
    # }
}
closedir $dir; 


# {
#     "sourceBoogie":"./test/BoogieProgram/sandbox.bpl",
#     "mutationRatio":[
# 	["S1",1],
# 	["S5",0],
# 	["S6",0],
# 	["S7",0],
# 	["G2",0],
# 	["G10",0],
# 	["L1",0],
# 	["L2",1]	
#     ],
#     "mutationLevels":10000,
#     "numberOfMutants":100,
#     "mutationAttempts":10000
# }
