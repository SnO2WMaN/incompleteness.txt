{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    devshell = {
      url = "github:numtide/devshell";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , ...
    } @ inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = with inputs; [
            devshell.overlays.default
          ];
        };
      in
      {
        devShells.default = pkgs.devshell.mkShell {
          packages = with pkgs; [
            nixpkgs-fmt
            typst
            typst-lsp
          ];
        };
      }
    );
}
