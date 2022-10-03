{ coqPackages }:

coqPackages.overrideScope' (
  self: super: {
    catala-formalization = self.callPackage ./catala-formalization.nix { };
})
