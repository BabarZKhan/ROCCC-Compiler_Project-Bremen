#!/usr/local/bin/perl

# This script generates the Makefile.deps file from a depedencies file
# generated by a Sun's cc.
# The Sun's cc generates a file with format different from that of gcc.
#
# Usage:
#  perl dep2make.pl < dependencies > Makefile.deps

$deps = {};
while ($line = <>) {
    chomp $line;
    while ($line =~ /\\$/) {
	my($next_line) = <>;
	if (!defined($next_line)) { last; }
	chomp($line);
	$line .= " $nextline";
    }

    my(@F) = split(/\s*:\s*/, $line);
    if ($#F < 1) { next; }
    my($file) = shift(@F);
    $file =~ s/://;
    if (!defined($deps->{$file})) {
	$deps->{$file} = [];
    }
    my($dep);
    foreach $dep (@F) {
      push(@{$deps->{$file}}, $dep);
    }
}
print "# Dependencies for C files\n";
print "\n";
print "CPP_TO_O_RULE = defined\n";
print "C_TO_O_RULE = defined\n\n";

foreach $file (keys(%{$deps})) {
    print "$file: ";
    print join(" ", @{$deps->{$file}}), "\n";
    my($first) = $deps->{$file}->[0];
    if ($first =~ /.cpp$/) {
      print "\t\$(CXX) \$(EXTRA_CXXFLAGS) ";
    } else {
	print "\t\$(CC) \$(EXTRA_CFLAGS) ";
    }
    print "-c -o $file \$(PROFILE_COMPILE) \$(COMPILER_SPECIFIC_CXXFLAGS) \\\n";
    print "\t\$(CCFLAGS) \$(INCLDIRS) \$(SYSINCLDIRS) \$(PREPROCESSORFLAGS) \\\n";
    print "\$(SUIF_MODULE) $first\n\n";
}
   
