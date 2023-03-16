{ pkgs ? import <nixpkgs> {} }: 

let agdaWithStdlib = pkgs.agda.withPackages (p: with p; [ standard-library ]); in
pkgs.mkShell {
  nativeBuildInputs = [ agdaWithStdlib ];
}