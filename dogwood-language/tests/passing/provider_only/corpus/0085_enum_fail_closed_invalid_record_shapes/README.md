# 0085_enum_fail_closed_invalid_record_shapes

A record output of the wrong shape denies (fail closed) when its type contains an enum: a bare id instead of the record, or a record missing its required enum field.

Polarity matters: the `forbid` only fires on HIGH. Without the shape check, each bad value would reach Cedar, which fails on `.result` and treats the `forbid` as not satisfied, so the `permit` would ALLOW the row (fail-open). Dogwood requires the provider error to DENY the request instead (those rows are `false`), with ``provider `MyGuardrails::ContentFilter`: expected a record, got a string`` (`bare`) and ``provider `MyGuardrails::ContentFilter`: missing required field `result` `` (`wrongkey`).
