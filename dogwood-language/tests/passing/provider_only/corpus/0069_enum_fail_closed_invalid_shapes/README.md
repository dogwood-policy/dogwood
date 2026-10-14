# 0069_enum_fail_closed_invalid_shapes

Unit, array, map, integer, bool and decimal at a scalar enum slot → DENY.

Polarity matters: the `forbid` only fires on HIGH. If an invalid value were
silently converted to a non-matching entity, the forbid would NOT fire and
each bad row would be ALLOWED (fail-open). Dogwood requires the provider error to
DENY the request instead (those rows are `false`).
