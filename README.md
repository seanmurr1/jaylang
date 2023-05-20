Jay Lang
=====

(Update: Oct 30, 2022)

This the the codebase for languages BlueJay, Jay and Jay Intermediate Language (JayIL), developped by JHU Programming Languages Lab. It's a pipeline of functional languages that fits for research at each layers.

This monorepo contains tools built upon these languages.

This was for the artifact for the paper **Higher-Order Demand-Driven Symbolic Evaluation**.

Install
-------

The repo is tested under MacOS, Ubuntu, and WSL on Windows.

Prepare and upgrade `apt` and the ocaml environment
```
sudo apt upgrade opam
opam update
```

Install local opam switch. Answer `yes` to questions. It can take a while.
This command installs the dependencies of this project to opam. You are supposed to develop in this directory.

If you also want to install this project to opam and develop external project, remove `--deps-only` from the command.

```
opam switch create ./ 4.14.1 --deps-only --description=jay-dev

# Sometimes opam fails due to parallel installation of packages. To fix it
opam install . --deps-only
```

After that, you can install the develop tools
```
opam user-setup install
opam install utop ocaml-lsp-server ocamlformat
```

Now you should be able to run the project.


Run
---

```
make dj
make dbmc
make sato
```

Concolic Tester
================

(Last updated: May 18th, 2023)

The concolic tester is an expansion upon the base JIL interpreter. Its main files are found in `/src/dbmc/concolic/`. The tester uses the Z3 OCaml module for constraint solving.

Related files:
---
- `/src/dbmc/concolic/concolic.ml`: concolic tester/interpreter.
- `/src/dbmc/concolic/concolic_feeder.ml`: logic to obtain an input feeder from a solved Z3 model.
- `/src-vendor/sudu/z3_api.ml`: wrapper module of base Z3, allowing for compatibility of untyped JIL variables.
- `/src/dbmc/riddler.ml`: helper functions to generate Z3 formulae given JIL variables.
- `/src/bin/jil.ml`: driver program to run normal interpreter or concolic tester.

Running the Concolic Tester:
---
Normal execution of interpreter:
```
dune exec src/bin/jil.exe -- -i <path to .jil file> -m normal <input feeder specification>
```

Concolic execution:
```
dune exec src/bin/jil.exe -- -i <path to .jil file> -m concolic
```

TODO:
---
- @Earl: implement "bubbling" up of abort exceptions when found.
- Model input dependency relations; optimize code.