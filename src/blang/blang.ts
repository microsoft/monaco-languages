 /*  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

import type { languages } from '../fillers/monaco-editor-core';

export const conf: languages.LanguageConfiguration = {
	comments: {
		lineComment: ' '
	},
	brackets: [
	],
	autoClosingPairs: [
	],
	surroundingPairs: [
	]
};

export const language = <languages.IMonarchLanguage>{
	defaultToken: '',
	tokenPostfix: '.blang',

	// we include these common regular expressions
	escapes: /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
	
	keywords: /say|add|ta|ram|inp|is|lop|div|mpy/,
	// The main tokenizer for our languages
	tokenizer: {
		root: [
			// whitespace
			{ include: '@whitespace' },

			// numbers
			[/\d+/, 'number'],
		],

		whitespace: [
			[/[ \t\r\n]+/, ''],
			[/^\s*[#;].*$/, 'comment']
		],
	}
};
