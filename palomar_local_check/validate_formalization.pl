#!/usr/bin/perl
# Mirror of the mechanical checks in PalomarSubmission scripts/submission_contract.py
# (commit 3561d237dcc4b28482558ad28a64d767d7cc8615), for local validation only.
use strict; use warnings; use utf8;
# YAML_TINY_LIB: directory containing YAML/Tiny.pm (YAML-Tiny 1.77, pure Perl).
use lib ($ENV{YAML_TINY_LIB} // '/tmp/perl5');
use YAML::Tiny; use JSON::PP;
binmode STDOUT, ':encoding(UTF-8)';
my ($file, $taxdir) = @ARGV;
my @err;
my $size = -s $file; push @err, "file larger than 256 KiB" if $size > 256*1024;
open my $fh, '<:encoding(UTF-8)', $file or die; my $raw = do { local $/; <$fh> }; close $fh;
# duplicate keys at any indentation within the same parent block (simple line scan)
# duplicate mapping keys: YAML::Tiny->read dies on them (checked below)
my $y = YAML::Tiny->read($file) or die "YAML parse error: " . YAML::Tiny->errstr;
my $d = $y->[0];
push @err, "top level is not a single mapping" unless @$y == 1 && ref $d eq 'HASH';
my $txt = sub { my ($v, $p, $max) = @_; if (!defined $v || ref $v || $v !~ /\S/) { push @err, "$p must be a nonempty string"; return } push @err, "$p exceeds $max chars" if $max && length($v) > $max; };
my $people = sub { my ($v,$p)=@_; if (ref $v ne 'ARRAY' || !@$v) { push @err, "$p must be a nonempty list"; return } for my $i (0..$#$v) { my $e=$v->[$i]; if (ref $e eq 'HASH') { $txt->($e->{name}, "$p\[$i].name") } else { $txt->($e, "$p\[$i]") } } };
my $pr = $d->{project} || {};
$txt->($pr->{name}, 'project.name', 300);
$txt->($pr->{description}, 'project.description', 10000);
$people->($pr->{authors}, 'project.authors');
$txt->($pr->{license}, 'project.license');
$people->($pr->{responsible_maintainers}, 'project.responsible_maintainers');
my $load = sub { open my $h, '<:raw', shift or die; local $/; decode_json(<$h>) };
my $arx = $load->("$taxdir/arxiv-categories.json"); my $msc = $load->("$taxdir/msc2020-codes.json");
my $cls = $d->{classification} || {};
my $chk = sub { my ($v,$p,$tax,$min,$max)=@_; $v //= []; if (ref $v ne 'ARRAY') { push @err, "$p must be a list"; return } push @err, "$p needs $min..$max entries" if @$v < $min || @$v > $max; my %u; for (@$v) { push @err, "$p: unknown code $_" unless exists $tax->{$_}; push @err, "$p: duplicate $_" if $u{$_}++ } };
$chk->($cls->{arxiv}, 'classification.arxiv', $arx, 1, 8);
$chk->($cls->{msc2020}, 'classification.msc2020', $msc, 0, 8);
my %SUB = map {$_=>1} qw(formalizes adapts independently-proves); my %CAT = (%SUB, background=>1, other=>1);
my $src = $d->{sources};
if (ref $src ne 'ARRAY' || !@$src) { push @err, "sources must be a nonempty list" } else {
  my ($orig, $subst, $origbad) = (0,0,0);
  for my $i (0..$#$src) { my $s = $src->[$i]; my $p="sources[$i]";
    if (ref $s ne 'HASH') { push @err, "$p must be a mapping"; next }
    $txt->($s->{title}, "$p.title"); $txt->($s->{relationship}, "$p.relationship", 500);
    my $rel = defined $s->{relationship} && $CAT{$s->{relationship}} ? $s->{relationship} : 'other';
    $txt->($s->{type}, "$p.type", 200) if exists $s->{type};
    $people->($s->{authors}, "$p.authors") if exists $s->{authors};
    for my $k (['id',2048],['location',1000],['note',10000],['license',500],['author_endorsement',100]) { $txt->($s->{$k->[0]}, "$p.$k->[0]", $k->[1]) if exists $s->{$k->[0]} }
    if (defined $s->{type} && $s->{type} eq 'original-proof') { $orig++; $origbad++ if $rel ne 'other' }
    $subst++ if $SUB{$rel};
  }
  if ($orig) { push @err, "original-proof must use relationship other" if $origbad; push @err, "original result cannot have substantive relationships" if $subst; print "result_origin: original\n" }
  else { push @err, "source-based result needs a substantive relationship" unless $subst; print "result_origin: source-based\n" }
}
my $rf = $d->{related_formalizations} // [];
if (ref $rf ne 'ARRAY') { push @err, "related_formalizations must be a list" } else { for my $i (0..$#$rf) { $txt->($rf->[$i]{id}, "related_formalizations[$i].id"); $txt->($rf->[$i]{relationship}, "related_formalizations[$i].relationship", 500) } }
my $m = ($d->{automation}||{})->{methods};
if (ref $m ne 'ARRAY' || !@$m) { push @err, "automation.methods must be a nonempty list" } else { for my $i (0..$#$m) { $txt->($m->[$i]{method}, "automation.methods[$i].method", 500) } }
$txt->(($d->{review}||{})->{status}, 'review.status');
push @err, "repository section present (should be omitted for substantive development)" if exists $d->{repository};
print "version: ", ($d->{version} // 'MISSING'), "\n";
print "license: $pr->{license}\n";
if (@err) { print "INVALID:\n", map {"  - $_\n"} @err; exit 1 } else { print "FORMALIZATION.YAML VALID (mechanical contract mirror)\n" }
