forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": [decimal("-376168898757656.9343"), decimal("-376168898757998.7064")]} else {"": [decimal("-393960623174.4768")]})[""]).containsAny([ip("::ffff:1f1f"), ip("0.0.0.0"), ip("0.0.0.0")]))) && false
};
