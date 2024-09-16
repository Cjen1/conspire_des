{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.opam-repository.follows = "opam-repository";
    };
    magic-trace-src = {
      url = "https://github.com/janestreet/magic-trace/releases/download/v1.2.3/magic-trace";
      flake = false;
    };
  };
  outputs = { self, flake-utils, opam-nix, nixpkgs, opam-repository, magic-trace-src}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        magic-trace = pkgs.stdenv.mkDerivation {
          name = "magic-trace";
          src = magic-trace-src;
          dontUnpack = true;

          buildInputs = [pkgs.makeWrapper];

          installPhase = ''
            mkdir -p $out/bin
            cp $src $out/bin/magic-trace
            chmod +x $out/bin/magic-trace
          '';

          postFixup = ''
          wrapProgram $out/bin/magic-trace \
            --set PATH ${pkgs.lib.makeBinPath [
              pkgs.fzf
              pkgs.linuxPackages_latest.perf
            ]}
          '';
        };

        on = opam-nix.lib.${system};
        devPackagesQuery = {
          ocaml-lsp-server = "*";
          #ocamlformat = "0.25.1";
          ocamlformat = "*";
          utop = "*";
        };
        repos = [
          opam-repository
        ];
        query = devPackagesQuery // {
          ocaml-base-compiler = "5.2.0";
          #ocaml-base-compiler = "5.1.0";
          #ocamlfind = "1.9.5";
        };
        scope = on.buildDuneProject { inherit repos; } "conspire_des" ./. query;
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames query) scope);
      in
      {
        defaultPackage = scope.conspire_des;
        devShell = pkgs.mkShell {
          inputsFrom = [scope.conspire_des];
          buildInputs = devPackages ++ [
            pkgs.linuxPackages_latest.perf
            magic-trace
          ];
        };
      });
}

