import * as React from 'react';
import { activityBarService, sidebarService } from 'molecule';
import { IExtension } from 'molecule/esm/model/extension';
import { IActivityBarItem } from 'molecule/esm/model';

import TestPane from './testPane';

export const ExtendTestPane: IExtension = {
	activate() {
		const testSidePane = {
			id: 'testPane',
			title: 'TEST',
			render() {
				return <TestPane />;
			}
		};

		sidebarService.push(testSidePane);
		const newItem = {
			id: 'ActivityBarTestPane',
			iconName: 'codicon-beaker',
			name: '测试'
		};
		activityBarService.addBar(newItem);

		activityBarService.onSelect((e, item: IActivityBarItem) => {
			if (item.id === newItem.id) {
				sidebarService.setState({
					current: testSidePane.id
				});
			}
		});
	}
};
