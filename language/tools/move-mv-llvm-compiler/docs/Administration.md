# This document describes the responsibilities of admins.

## Keep up with the upstream

### Update codebase
[Weekly] Check for patches [upstream](https://github.com/move-language/move) that
have been merged to the main branch.

### Track issues
[Weekly] Check issues in [move-upstream](https://github.com/move-language/move/issues) that
might be of interest to our compiler.

## Code Reviews
[Frequently] Make sure each patch is merged with proper reviews.

## Issue tracking
[Frequently] Try to have tasks for as many PR as possible. Encourage contributors
to link issue with their PR.

[Weekly] Close out issues that are fixed.

## Communication

### Discord
[Frequently] Visit solana-labs/#proj-move discord channel.

[Frequently] Visit relevant move-language, sui, and aptos discord channels.

[As needed] Update solana-labs/#proj-move of major updates.

## Migration
### Toolchain migration to keep up with solana platform tools and move-dev tools
1. Update toolchain versions in scripts/acquire_solana_tools.sh, .github/actions/acquire-solana-tools/action.yml
1. Update LLVM_SYS_{VER}_PREFIX to the correct version
1. Update the versions in documents
1. Fix all build errors
1. Fix all tests
1. Announce in discord

### Upgrading llvm-sys
1. Create a github issue to track the progress
1. `grep` for all llvm-sys deps and migrate all of them at once (e.g. Cargo.lock files)
1. Fix build errors
1. Update the documentation
1. Update the ci scripts
1. Announce in discord
