{ coqPackages }:

coqPackages.overrideScope' (
  self: super: {
    catala = self.callPackage ./catala.nix { };
})
