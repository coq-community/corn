{ pkgs ? (import <nixpkgs> {}), coq-version-or-url, shell ? false }:

let
  coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version-or-url;
  coqPackages =
    if coq-version-parts == null then
      pkgs.mkCoqPackages (import (fetchTarball coq-version-or-url) {})
    else
      pkgs."coqPackages_${builtins.concatStringsSep "_" coq-version-parts}";
in

let math-classes = coqPackages.math-classes.overrideAttrs (o: {
    src = fetchTarball "https://github.com/coq-community/math-classes/archive/master.tar.gz";
  }); in

let inherit (coqPackages) coq bignums; in

pkgs.stdenv.mkDerivation {

  name = "corn";

  propagatedBuildInputs = [
    coq
    math-classes
    bignums
  ];

  src = if shell then null else ./.;

  configurePhase = "./configure.sh";

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}
