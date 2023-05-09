{ lib
, mkCoqDerivation
, coq
, coq-elpi
, autosubst
}:

mkCoqDerivation {
  pname = "catala";
  src = ../.;
  useDune = true;

  version = "0.1.0";

  propagatedBuildInputs = [
    autosubst
    coq-elpi
  ];

  meta = {
    description = "Work in progress formalization for the Catala programming language";
  };
}
