# This is copied from Yael Dillies Toric project
# Build HTML documentation for pi1
# The output will be located in docs/build

# Template lakefile.toml
template() {
  cat <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "pi1"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "TOOLCHAIN"
EOF
}

# Create a temporary docbuild folder
mkdir -p docbuild

# Equip docbuild with the template lakefile.toml
template > docbuild/lakefile.toml

# Substitute the toolchain from lean-toolchain into docbuild/lakefile.toml
sed -i s/TOOLCHAIN/`grep -oP 'v4\..*' lean-toolchain`/ docbuild/lakefile.toml

# Fetch the docs cache if it exists
mkdir -p docs/build
mkdir -p docbuild/.lake/build/doc
mv docs/build/* docbuild/.lake/build/doc

# Initialise docbuild as a Lean project
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1
~/.elan/bin/lake update Pi1
~/.elan/bin/lake exe cache get

# Build the docs
~/.elan/bin/lake build Pi1:docs

# Move them out of docbuild
cd ../
mkdir -p docs/build
mv docbuild/.lake/build/doc/* docs/build

# Clean up after ourselves
rm -rf docbuild
