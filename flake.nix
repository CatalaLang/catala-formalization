{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = {nixpkgs, flake-utils, ...}:
    let
      systems = [ "x86_64-linux" ];
    in flake-utils.lib.eachSystem systems (system:
      let
        pkgs = import nixpkgs { inherit system; };
        self_pkgs = pkgs.callPackage ./nix/packages.nix {
          coqPackages=pkgs.coqPackages_8_16;
        };
        python3 = pkgs.python3;
      in
      rec {
        packages = with self_pkgs; {
          catala = coqPackages.catala;
          default = coqPackages.catala;
        };
        devShell = pkgs.mkShell {
          inputsFrom = [ packages.catala ];
          buildInputs = [
            self_pkgs.coqPackages.serapi
            python3.pkgs.alectryon
            python3.pkgs.rich
            pkgs.texlive.combined.scheme-full
          ];
        };
      }
    );
}
