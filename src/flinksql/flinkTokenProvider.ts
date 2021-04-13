import * as monaco from 'monaco-editor';

import ILineTokens = monaco.languages.ILineTokens;
import IToken = monaco.languages.IToken;

class FLinkTokensProvider implements monaco.languages.TokensProvider {
	getInitialState(): monaco.languages.IState {
		throw new Error('Method not implemented.');
	}
	tokenize(line: string, state: monaco.languages.IState): monaco.languages.ILineTokens {
		throw new Error('Method not implemented.');
	}
}
