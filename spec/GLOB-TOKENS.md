# Certified raw glob tokens

`GlobTokens` connects raw glob bodies to the existing matcher atoms. Its
independent `Source` relation covers literals, quoting, question marks, ordinary
stars, recursive stars, compiled character classes and group punctuation.

## Closed token meanings

A closed keyword catalogue and its coverage proof drive character classification.
Ordinary characters carry evidence that they are outside that catalogue.
Recursive wildcards have explicit source-position and group context: directory
prefixes consume their slash, and terminal recursive stars leave group separators
for the surrounding parser. Other stars retain ordinary separator-free meaning.

Class tokens retain the actual lexical and range certificates. An unclosed class
is a literal opening bracket only when the lexical grammar proves no class is
present. An unordered interval cannot silently become that literal fallback.

## General laws

`scan` is total. Every returned token carries its source derivation. `recognized`
proves that every source derivation is recognized; `deterministic` proves token
and suffix meaning is unique. `consumption` reconstructs the original source as
a consumed prefix and saved suffix. `progress` proves the suffix is strictly
shorter, providing the decreasing measure needed by complete body parsing.

These laws quantify over arbitrary input and parser context. They introduce no
pattern fixtures, arbitrary iteration limits or terminal product-failure state.
Private parser absence belongs to the existing corrective dialogue.

## Boundary

This closes #130, a bounded part of #26. Whole-body sequencing and brace
assembly must still supply the actual position/group context. Rule framing,
Git-default/Muninn-override precedence, ignored-parent traversal and integration
with indexing, search and cleanup remain required under #26.

This changes Agda and documentation only. It is not a Rust correspondence proof
or a claim that the installed implementation now follows these rules.
