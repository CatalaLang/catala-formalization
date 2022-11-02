{
  inputs = {
    flake-utils.url = github:numtide/flake-utils;
    nixpkgs.url = github:NixOS/nixpkgs/nixos-unstable;
  };

  outputs = {nixpkgs, flake-utils, ...}:
    let
      systems = [ "x86_64-linux" ];
    in flake-utils.lib.eachSystem systems (system:
      let
        pkgs = import nixpkgs { inherit system; };
        self_pkgs = pkgs.callPackage ./nix/packages.nix {};
        python3 = pkgs.python3;
      in
      rec {
        packages = with self_pkgs; {
          catala = coqPackages.catala;
          catala_8_5 = coqPackages_8_5.catala;
          catala_8_6 = coqPackages_8_6.catala;
          catala_8_7 = coqPackages_8_7.catala;
          catala_8_8 = coqPackages_8_8.catala;
          catala_8_9 = coqPackages_8_9.catala;
          catala_8_10 = coqPackages_8_10.catala;
          catala_8_11 = coqPackages_8_11.catala;
          catala_8_12 = coqPackages_8_12.catala;
          catala_8_13 = coqPackages_8_13.catala;
          catala_8_14 = coqPackages_8_14.catala;
          catala_8_15 = coqPackages_8_15.catala;
          catala_8_16 = coqPackages_8_16.catala;
          default = coqPackages.catala;
        };
        devShell = pkgs.mkShell {
          inputsFrom = [ packages.catala ];
          buildInputs = [
            pkgs.coqPackages.serapi
            python3.pkgs.alectryon
          ];
        };
      }
    );
}
