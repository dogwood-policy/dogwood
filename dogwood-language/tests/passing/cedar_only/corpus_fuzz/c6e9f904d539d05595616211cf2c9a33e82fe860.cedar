@g(">>>>>>")
permit(
  principal in jz::a::"",
  action == jz::Action::"action",
  resource in jz::a::""
) when {
  (true && (if (if (action has "UUUUUUUUUUUUUUUUUUUUUUU>>>>>>") then (if true then true else true) else (if false then false else false)) then ((decimal("UUU")).lessThan(decimal("UUU"))) else ((decimal("UUUUUUUUUUUUUUUUUUUUUUU>>>>>>")).lessThan(decimal("UUUUUUUUUUUUUUUUUUUUUUU>>>>>>"))))) && true
};
