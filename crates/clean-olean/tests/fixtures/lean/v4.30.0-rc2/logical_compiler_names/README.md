# Logical names resembling compiler auxiliaries

The pinned Lean compiles this ordinary source through the maintained content
addressed fixture helper. All declarations are safe; the module system exports
ordinary definitions as axiom stubs and keeps their values in the private part.
The tests compare exact typed projection names, retain safe definitions and
namespace components resembling old compiler output, and corrupt a projection
or source safety to confirm that the existing artifact/projection guards refuse.

`_spec_1` and `_elambda_1` occur as namespace components. Separate official435
attempts with these as final declaration names emitted normalized-name PANICs
even with exit0; those diagnostics are evidence, not successful source controls.
Synthetic exporter tests independently exercise such exact final Name components
without claiming that the external frontend accepted those source spellings.
