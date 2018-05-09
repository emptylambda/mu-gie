#!/usr/bin/perl
use strict;
use warnings;
use Cwd;
use File::chdir; 

opendir my $dir, getcwd() or die "cannot open directory";
my @cores = readdir $dir;
if($line =~ /MatchText/){
    $line =~ s/ReplaceMe/REPLACED/gi;
}
