{
  description = "docker image";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: {
    packages.x86_64-linux.default = nixpkgs.legacyPackages.x86_64-linux.callPackage ./docker.nix {name = "ghcr.io/CatalaLang/catala-coq-ci";};
  };
}
