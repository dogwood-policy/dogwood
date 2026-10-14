# 0070_enum_fail_closed_bad_set_element

One non-member inside a Set<enum> output fails the whole value → DENY.

Polarity matters: the `forbid` only fires on HIGH. If an invalid value were
silently converted to a non-matching entity, the forbid would NOT fire and
`boom` would be ALLOWED (fail-open). Dogwood requires the provider error to
DENY the request instead (`@10 … false`).
