with (import <nixpkgs> {});
mkShell {
  buildInputs = [
    opam
    dune_3
    ocaml
    ocamlPackages.ocaml-lsp
    ocamlPackages.utop
    ocamlPackages.ounit2
    ocamlPackages.ocamlformat
  ];
  shellHook =
  ''
    dune build @install --profile=release
  '';
}