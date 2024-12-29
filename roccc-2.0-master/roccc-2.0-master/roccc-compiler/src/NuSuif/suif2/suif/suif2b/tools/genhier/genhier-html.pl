#!/usr/bin/perl -w

use strict;

# The stuff is store in a hash of lists
my %children = ();

# not a root
my %aroot = ();

sub print_hier
{
  my $obj = shift;
  my $indent = shift || 0;
  print "<li><b> ";
  print $obj . "</b>. \n";

  if (defined $children{$obj}) {
    print "<ul> ";
    print "\n";
    foreach my $subclass (sort @ {$children{$obj}}) {
      &print_hier($subclass, $indent + 4);
    }
    print "</ul> ";
    print "\n";
  }
}

while (<>) {
  # Get rid of comments
  s/\#.*//;

  # $3 -> $1
  # $1 has a parent 
  if (/(\w+)\s*(\[.*\])?\s*:\s*(\w+)/) {
    $aroot{$1} = 0;
    if (!defined $aroot{$3}) {
      $aroot{$3} = 1;
      push @ { $children{"all"} }, $3;
    }
    if (!defined $children{$3}) {
      $children{$3} = [ $1 ];
    } else {
      push @ { $children{$3} }, $1;
    }
  }
}
print "<ul>\n"; 
foreach my $root ( sort @ {$children{"all"}} ) {
    if ($aroot{$root}) {&print_hier($root)};
}
print "</ul>\n"; 





