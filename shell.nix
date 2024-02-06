with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    opam
    dune_3
    ocamlPackages.ocaml-lsp
    ocaml
    ocamlPackages.ocamlformat
  ];
  shellHook =
  ''
    dune build @install
  '';
}