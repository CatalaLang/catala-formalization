{ coqPackages
, coqPackages_8_5
, coqPackages_8_6
, coqPackages_8_7
, coqPackages_8_8
, coqPackages_8_9
, coqPackages_8_10
, coqPackages_8_11
, coqPackages_8_12
, coqPackages_8_13
, coqPackages_8_14
, coqPackages_8_15
, coqPackages_8_16 }:

{
  coqPackages_8_5 = coqPackages_8_5.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_6 = coqPackages_8_6.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_7 = coqPackages_8_7.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_8 = coqPackages_8_8.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_9 = coqPackages_8_9.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_10 = coqPackages_8_10.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_11 = coqPackages_8_11.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_12 = coqPackages_8_12.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_13 = coqPackages_8_13.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_14 = coqPackages_8_14.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_15 = coqPackages_8_15.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages_8_16 = coqPackages_8_16.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
  coqPackages = coqPackages.overrideScope' (self: super: {catala=self.callPackage ./catala.nix {};});
}
