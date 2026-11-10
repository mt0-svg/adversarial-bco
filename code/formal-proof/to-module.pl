#!/usr/bin/env perl
# Converts Lean files to the module system, mechanically: `module` before the first import (or at the top of a
# file with no import), every import public, and `@[expose] public section` after the imports, so that every
# declaration stays public and every definition keeps its body visible to importers, as without modules. With
# modules, Lake recompiles the importers of a file only when its public interface changes: a comment or docstring
# edit recompiles that file alone. Files that already start with `module` are left as they are.
# Usage: code/formal-proof/to-module.pl FILE.lean ...   (in place), e.g. on `git ls-files 'AdversarialBco/*.lean'`
use strict; use warnings;
for my $f (@ARGV) {
  open my $h, '<', $f or die "$f: $!"; my @l = <$h>; close $h;
  next if grep { /^module\s*$/ } @l;
  my ($first, $last);
  # The import block: the import lines before the first line of code, comments and blank lines skipped (a line of a
  # comment that starts with "import" is not one).
  my $depth = 0;
  for my $i (0 .. $#l) {
    my $s = $l[$i];
    if ($depth > 0 || $s =~ m{^\s*/-}) { $depth += () = $s =~ m{/-}g; $depth -= () = $s =~ m{-/}g; next }
    next if $s =~ /^\s*(--.*)?$/;
    if ($s =~ /^import\s/) { $first //= $i; $last = $i; next }
    last;
  }
  unless (defined $first) { my $i = 0; $i++ while $i < $#l && ($l[$i] =~ /^\s*$/ || $l[$i] =~ /^\s*--/); $first = $i; $last = $i - 1 }
  s/^import\s/public import / for @l[$first .. $last];
  splice @l, $last + 1, 0, "\n\@[expose] public section\n";
  splice @l, $first, 0, "module\n\n";
  open $h, '>', $f or die; print $h @l; close $h;
}
