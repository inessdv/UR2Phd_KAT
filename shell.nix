with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    opam
    dune_3
    ocamlPackages.ocaml-lsp
    ocaml
  ];
  shellHook =
  ''
    dune build @install
  '';
}