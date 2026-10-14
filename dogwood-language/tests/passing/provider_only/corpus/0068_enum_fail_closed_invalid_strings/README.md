# 0068_enum_fail_closed_invalid_strings

An undeclared value (`CRITICAL`), wrong case, padding, empty string and full-UID text are all non-members → DENY. The script must return the BARE id.

Polarity matters: the `forbid` only fires on HIGH. If an invalid value were
silently converted to a non-matching entity, the forbid would NOT fire and
each bad row would be ALLOWED (fail-open). Dogwood requires the provider error to
DENY the request instead (those rows are `false`).
