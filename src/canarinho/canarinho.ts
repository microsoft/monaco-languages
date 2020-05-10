/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

'use strict';

import { conf as tsConf, language as tsLanguage } from '../typescript/typescript';
import IRichLanguageConfiguration = monaco.languages.LanguageConfiguration;
import ILanguage = monaco.languages.IMonarchLanguage;

// Allow for running under nodejs/requirejs in tests
const _monaco: typeof monaco = (typeof monaco === 'undefined' ? (<any>self).monaco : monaco);

export const conf: IRichLanguageConfiguration = tsConf;

export const language = <ILanguage>{
	// Set defaultToken to invalid to see what you do not tokenize yet
	defaultToken: 'invalid',
	tokenPostfix: '.cnr',

	keywords: [
		"caso seja", "classe", "construtor",
		"em caso inesperado", "em_maiusculo", "em_minusculo", "enquanto",
		"falso", "funcao", "imprimir", "importar", "instanciar", "instancia",
		"metodo", "nulo", "ou entao", "parar", "retornar",
		"se", "senao", "variavel", "verdadeiro", "verificar",
	],
	typeKeywords: [],

	operators: tsLanguage.operators,
	symbols: tsLanguage.symbols,
	escapes: tsLanguage.escapes,
	digits: tsLanguage.digits,
	octaldigits: tsLanguage.octaldigits,
	binarydigits: tsLanguage.binarydigits,
	hexdigits: tsLanguage.hexdigits,
	regexpctl: tsLanguage.regexpctl,
	regexpesc: tsLanguage.regexpesc,
	tokenizer: tsLanguage.tokenizer,
};
