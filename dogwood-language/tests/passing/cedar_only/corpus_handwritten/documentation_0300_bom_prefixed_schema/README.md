# BOM-prefixed schema and policy

Both `schema.cedarschema` and `policy_1.dw` begin with a UTF-8 BOM
(U+FEFF, encoded as EF BB BF). Windows editors (Notepad, VS Code with
certain settings, PowerShell `Out-File`) prepend this byte sequence.

Dogwood strips it at every entry point so users never hit a confusing
"unexpected token" error from Cedar's schema parser or from the policy
parser itself.

## Verifying the BOM is present

The BOM is invisible in editors. To confirm the files still have it:

```bash
xxd schema.cedarschema | head -1
# Expected: efbb bf6e 616d 6573 ...  (first 3 bytes are EF BB BF)

xxd policy_1.dw | head -1
# Expected: efbb bf70 6572 6d69 ...  (first 3 bytes are EF BB BF)
```

If a tool or editor strips the BOM, restore it with:

```bash
printf '\xEF\xBB\xBF' | cat - <(cat schema.cedarschema) > tmp && mv tmp schema.cedarschema
printf '\xEF\xBB\xBF' | cat - <(cat policy_1.dw) > tmp && mv tmp policy_1.dw
```
