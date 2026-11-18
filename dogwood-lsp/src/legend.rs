pub const TOKEN_TYPES: [&str; 19] = [
    "namespace",
    "type",
    "struct",
    "typeParameter",
    "parameter",
    "variable",
    "property",
    "enumMember",
    "event",
    "function",
    "method",
    "macro",
    "keyword",
    "modifier",
    "comment",
    "string",
    "number",
    "operator",
    "decorator",
];

pub const TOKEN_MODIFIERS: [&str; 1] = ["declaration"];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TokenKind {
    Namespace,
    Type,
    Struct,
    TypeParameter,
    Parameter,
    Variable,
    Property,
    EnumMember,
    Event,
    Function,
    Method,
    Macro,
    Keyword,
    Modifier,
    Comment,
    String,
    Number,
    Operator,
    Decorator,
    Punctuation,
}

impl TokenKind {
    pub const fn legend_index(self) -> u32 {
        match self {
            Self::Namespace => 0,
            Self::Type => 1,
            Self::Struct => 2,
            Self::TypeParameter => 3,
            Self::Parameter => 4,
            Self::Variable => 5,
            Self::Property => 6,
            Self::EnumMember => 7,
            Self::Event => 8,
            Self::Function => 9,
            Self::Method => 10,
            Self::Macro => 11,
            Self::Keyword => 12,
            Self::Modifier => 13,
            Self::Comment => 14,
            Self::String => 15,
            Self::Number => 16,
            Self::Operator | Self::Punctuation => 17,
            Self::Decorator => 18,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TokenModifier {
    Declaration,
}

impl TokenModifier {
    pub const fn legend_index(self) -> u32 {
        match self {
            Self::Declaration => 0,
        }
    }

    pub const fn legend_bit(self) -> u32 {
        1 << self.legend_index()
    }
}

#[cfg(test)]
mod tests {
    use super::{TOKEN_MODIFIERS, TOKEN_TYPES, TokenKind, TokenModifier};

    #[test]
    fn legend_order_is_frozen() {
        assert_eq!(
            TOKEN_TYPES,
            [
                "namespace",
                "type",
                "struct",
                "typeParameter",
                "parameter",
                "variable",
                "property",
                "enumMember",
                "event",
                "function",
                "method",
                "macro",
                "keyword",
                "modifier",
                "comment",
                "string",
                "number",
                "operator",
                "decorator",
            ]
        );
        assert_eq!(TOKEN_MODIFIERS, ["declaration"]);
    }

    #[test]
    fn every_kind_maps_to_the_frozen_legend() {
        let mappings = [
            (TokenKind::Namespace, 0),
            (TokenKind::Type, 1),
            (TokenKind::Struct, 2),
            (TokenKind::TypeParameter, 3),
            (TokenKind::Parameter, 4),
            (TokenKind::Variable, 5),
            (TokenKind::Property, 6),
            (TokenKind::EnumMember, 7),
            (TokenKind::Event, 8),
            (TokenKind::Function, 9),
            (TokenKind::Method, 10),
            (TokenKind::Macro, 11),
            (TokenKind::Keyword, 12),
            (TokenKind::Modifier, 13),
            (TokenKind::Comment, 14),
            (TokenKind::String, 15),
            (TokenKind::Number, 16),
            (TokenKind::Operator, 17),
            (TokenKind::Decorator, 18),
        ];

        for (kind, expected_index) in mappings {
            assert_eq!(kind.legend_index(), expected_index);
        }
    }

    #[test]
    fn punctuation_maps_to_operator() {
        assert_ne!(TokenKind::Punctuation, TokenKind::Operator);
        assert_eq!(
            TokenKind::Punctuation.legend_index(),
            TokenKind::Operator.legend_index()
        );
        assert_eq!(
            TOKEN_TYPES[TokenKind::Punctuation.legend_index() as usize],
            "operator"
        );
    }

    #[test]
    fn declaration_uses_modifier_index_zero_and_bit_zero() {
        assert_eq!(TokenModifier::Declaration.legend_index(), 0);
        assert_eq!(TokenModifier::Declaration.legend_bit(), 1);
    }
}
